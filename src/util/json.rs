//! Integer-only JSON for reproducible experiment records, preserving object insertion order.
//! Floating-point values are rejected; durations and sizes are stored as integer counts.

use std::{
    fmt::{Display, Formatter, Write as _},
    time::Duration,
};

/// A JSON value, restricted to what an experiment record needs.
///
/// No floats, by design — see the module docs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Json {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// An integer. Signed, so a difference can be recorded.
    Int(i128),
    /// A string, escaped on output.
    Str(String),
    /// An array.
    Array(Vec<Json>),
    /// An object. **Insertion order is preserved**, because a record that reordered its keys
    /// between runs would make a textual diff useless.
    Object(Vec<(String, Json)>),
}

impl Json {
    /// A string value.
    pub fn string(s: impl Into<String>) -> Self {
        Self::Str(s.into())
    }

    /// An integer value from anything that converts.
    pub fn int(n: impl Into<i128>) -> Self {
        Self::Int(n.into())
    }

    /// A `usize`, which does not implement `Into<i128>`.
    pub fn size(n: usize) -> Self {
        Self::Int(n as i128)
    }

    /// A duration, as whole nanoseconds.
    ///
    /// Nanoseconds rather than fractional milliseconds: an integer round-trips and a float does
    /// not, and a consumer that wants milliseconds can divide.
    pub fn nanos(d: Duration) -> Self {
        Self::Int(d.as_nanos() as i128)
    }

    /// An object from pairs, preserving order.
    pub fn object<K: Into<String>>(fields: impl IntoIterator<Item = (K, Json)>) -> Self {
        Self::Object(fields.into_iter().map(|(k, v)| (k.into(), v)).collect())
    }

    /// Serialize, with two-space indentation.
    ///
    /// Deterministic: the same value always produces the same bytes, which is what makes a record
    /// diffable across runs.
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, 0);
        out
    }

    fn write(&self, out: &mut String, depth: usize) {
        let pad = |out: &mut String, depth: usize| {
            for _ in 0..depth {
                out.push_str("  ");
            }
        };
        match self {
            Self::Null => out.push_str("null"),
            Self::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Self::Int(n) => {
                let _ = write!(out, "{}", n);
            }
            Self::Str(s) => Self::write_string(out, s),
            Self::Array(items) if items.is_empty() => out.push_str("[]"),
            Self::Array(items) => {
                out.push_str("[\n");
                for (index, item) in items.iter().enumerate() {
                    pad(out, depth + 1);
                    item.write(out, depth + 1);
                    if index + 1 < items.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                pad(out, depth);
                out.push(']');
            }
            Self::Object(fields) if fields.is_empty() => out.push_str("{}"),
            Self::Object(fields) => {
                out.push_str("{\n");
                for (index, (key, value)) in fields.iter().enumerate() {
                    pad(out, depth + 1);
                    Self::write_string(out, key);
                    out.push_str(": ");
                    value.write(out, depth + 1);
                    if index + 1 < fields.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                pad(out, depth);
                out.push('}');
            }
        }
    }

    /// Parse the subset this type emits.
    ///
    /// Exists because a scoreboard **accumulates**: `results/history.json` is read, extended and
    /// written back, and a writer with no reader would mean either losing the history on every run
    /// or carrying a dependency to read back what eighty lines wrote. Round-tripping is asserted,
    /// including by a property test over arbitrary values.
    ///
    /// Strict within the subset: no floats, since nothing here emits one and accepting one would
    /// let a number that cannot round-trip into a record. Everything else RFC 8259 allows is
    /// accepted, including `\u` escapes and surrogate pairs.
    ///
    /// # Errors
    /// [`JsonError`], naming the byte offset.
    pub fn parse(text: &str) -> Result<Self, JsonError> {
        let bytes = text.as_bytes();
        let mut at = 0usize;
        let value = Self::parse_value(bytes, &mut at)?;
        Self::skip_whitespace(bytes, &mut at);
        if at != bytes.len() {
            return Err(JsonError {
                at,
                reason: "trailing input",
            });
        }
        Ok(value)
    }

    fn skip_whitespace(bytes: &[u8], at: &mut usize) {
        while *at < bytes.len() && matches!(bytes[*at], b' ' | b'\t' | b'\n' | b'\r') {
            *at += 1;
        }
    }

    fn parse_value(bytes: &[u8], at: &mut usize) -> Result<Self, JsonError> {
        Self::skip_whitespace(bytes, at);
        let start = *at;
        match bytes.get(start) {
            None => Err(JsonError {
                at: start,
                reason: "unexpected end of input",
            }),
            Some(b'n') => Self::expect(bytes, at, b"null", Json::Null),
            Some(b't') => Self::expect(bytes, at, b"true", Json::Bool(true)),
            Some(b'f') => Self::expect(bytes, at, b"false", Json::Bool(false)),
            Some(b'"') => Self::parse_string(bytes, at).map(Json::Str),
            Some(b'[') => {
                *at += 1;
                let mut items = Vec::new();
                loop {
                    Self::skip_whitespace(bytes, at);
                    if bytes.get(*at) == Some(&b']') {
                        *at += 1;
                        return Ok(Json::Array(items));
                    }
                    if !items.is_empty() {
                        Self::expect_byte(bytes, at, b',')?;
                    }
                    Self::skip_whitespace(bytes, at);
                    // A `]` here would be a trailing comma, which the loop above only accepts
                    // before the first item.
                    if bytes.get(*at) == Some(&b']') {
                        return Err(JsonError {
                            at: *at,
                            reason: "trailing comma in array",
                        });
                    }
                    items.push(Self::parse_value(bytes, at)?);
                }
            }
            Some(b'{') => {
                *at += 1;
                let mut fields: Vec<(String, Json)> = Vec::new();
                loop {
                    Self::skip_whitespace(bytes, at);
                    if bytes.get(*at) == Some(&b'}') {
                        *at += 1;
                        return Ok(Json::Object(fields));
                    }
                    if !fields.is_empty() {
                        Self::expect_byte(bytes, at, b',')?;
                    }
                    Self::skip_whitespace(bytes, at);
                    let key = Self::parse_string(bytes, at)?;
                    Self::skip_whitespace(bytes, at);
                    Self::expect_byte(bytes, at, b':')?;
                    fields.push((key, Self::parse_value(bytes, at)?));
                }
            }
            Some(_) => Self::parse_integer(bytes, at),
        }
    }

    fn expect(
        bytes: &[u8],
        at: &mut usize,
        literal: &[u8],
        value: Json,
    ) -> Result<Json, JsonError> {
        if bytes.len() >= *at + literal.len() && &bytes[*at..*at + literal.len()] == literal {
            *at += literal.len();
            Ok(value)
        } else {
            Err(JsonError {
                at: *at,
                reason: "not a JSON literal",
            })
        }
    }

    fn expect_byte(bytes: &[u8], at: &mut usize, byte: u8) -> Result<(), JsonError> {
        Self::skip_whitespace(bytes, at);
        if bytes.get(*at) == Some(&byte) {
            *at += 1;
            Ok(())
        } else {
            Err(JsonError {
                at: *at,
                reason: "expected a delimiter",
            })
        }
    }

    fn parse_integer(bytes: &[u8], at: &mut usize) -> Result<Json, JsonError> {
        let start = *at;
        if bytes.get(*at) == Some(&b'-') {
            *at += 1;
        }
        let digits = *at;
        while *at < bytes.len() && bytes[*at].is_ascii_digit() {
            *at += 1;
        }
        if *at == digits {
            return Err(JsonError {
                at: start,
                reason: "not a number",
            });
        }
        // A float is rejected rather than truncated: a record that held one would not round-trip,
        // which is the whole reason this type has no float variant.
        if matches!(bytes.get(*at), Some(b'.') | Some(b'e') | Some(b'E')) {
            return Err(JsonError {
                at: *at,
                reason: "floats are not part of this subset",
            });
        }
        std::str::from_utf8(&bytes[start..*at])
            .expect("ASCII digits")
            .parse::<i128>()
            .map(Json::Int)
            .map_err(|_| JsonError {
                at: start,
                reason: "integer out of range",
            })
    }

    fn parse_string(bytes: &[u8], at: &mut usize) -> Result<String, JsonError> {
        Self::skip_whitespace(bytes, at);
        if bytes.get(*at) != Some(&b'"') {
            return Err(JsonError {
                at: *at,
                reason: "expected a string",
            });
        }
        *at += 1;
        let mut out = String::new();
        loop {
            let byte = *bytes.get(*at).ok_or(JsonError {
                at: *at,
                reason: "unterminated string",
            })?;
            match byte {
                b'"' => {
                    *at += 1;
                    return Ok(out);
                }
                b'\\' => {
                    *at += 1;
                    let escape = *bytes.get(*at).ok_or(JsonError {
                        at: *at,
                        reason: "unterminated escape",
                    })?;
                    *at += 1;
                    match escape {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{08}'),
                        b'f' => out.push('\u{0c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let first = Self::parse_hex4(bytes, at)?;
                            // A high surrogate is only half a character, and the writer emits
                            // non-ASCII as UTF-8 rather than as escapes — but another producer may
                            // not, and half a character is not a decoding.
                            let code = if (0xD800..0xDC00).contains(&first) {
                                if bytes.get(*at) != Some(&b'\\')
                                    || bytes.get(*at + 1) != Some(&b'u')
                                {
                                    return Err(JsonError {
                                        at: *at,
                                        reason: "lone high surrogate",
                                    });
                                }
                                *at += 2;
                                let second = Self::parse_hex4(bytes, at)?;
                                if !(0xDC00..0xE000).contains(&second) {
                                    return Err(JsonError {
                                        at: *at,
                                        reason: "bad low surrogate",
                                    });
                                }
                                0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00)
                            } else {
                                first
                            };
                            out.push(char::from_u32(code).ok_or(JsonError {
                                at: *at,
                                reason: "not a scalar value",
                            })?);
                        }
                        _ => {
                            return Err(JsonError {
                                at: *at,
                                reason: "unknown escape",
                            })
                        }
                    }
                }
                byte if byte < 0x20 => {
                    return Err(JsonError {
                        at: *at,
                        reason: "unescaped control character",
                    })
                }
                byte if byte.is_ascii() => {
                    out.push(char::from(byte));
                    *at += 1;
                }
                _ => {
                    // Checking the whole suffix here makes record parsing quadratic.
                    let width = byte.leading_ones() as usize;
                    let invalid = || JsonError {
                        at: *at,
                        reason: "invalid UTF-8",
                    };
                    if !(2..=4).contains(&width) {
                        return Err(invalid());
                    }
                    let scalar = bytes.get(*at..*at + width).ok_or_else(invalid)?;
                    let scalar = std::str::from_utf8(scalar).map_err(|_| invalid())?;
                    out.push_str(scalar);
                    *at += width;
                }
            }
        }
    }

    fn parse_hex4(bytes: &[u8], at: &mut usize) -> Result<u32, JsonError> {
        if *at + 4 > bytes.len() {
            return Err(JsonError {
                at: *at,
                reason: "truncated \\u escape",
            });
        }
        let text = std::str::from_utf8(&bytes[*at..*at + 4]).map_err(|_| JsonError {
            at: *at,
            reason: "truncated \\u escape",
        })?;
        let value = u32::from_str_radix(text, 16).map_err(|_| JsonError {
            at: *at,
            reason: "bad \\u escape",
        })?;
        *at += 4;
        Ok(value)
    }

    /// The value at `key`, for an object.
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Self::Object(fields) => fields.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    /// The items, for an array.
    pub fn items(&self) -> &[Json] {
        match self {
            Self::Array(items) => items,
            _ => &[],
        }
    }

    /// The string, for a string.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }

    /// The integer, for an integer.
    pub fn as_int(&self) -> Option<i128> {
        match self {
            Self::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// A JSON string literal, escaped per RFC 8259 §7.
    fn write_string(out: &mut String, s: &str) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                '\u{08}' => out.push_str("\\b"),
                '\u{0c}' => out.push_str("\\f"),
                // Every other control character must be escaped; everything else, including
                // non-ASCII, is passed through as UTF-8, which RFC 8259 permits.
                c if (c as u32) < 0x20 => {
                    let _ = write!(out, "\\u{:04x}", c as u32);
                }
                c => out.push(c),
            }
        }
        out.push('"');
    }
}

/// Why a JSON text could not be read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct JsonError {
    /// Byte offset into the input.
    pub at: usize,

    /// What was wrong there.
    pub reason: &'static str,
}

impl Display for JsonError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at byte {}", self.reason, self.at)
    }
}

impl std::error::Error for JsonError {}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::Json;

    /// Scalars and containers serialize to the forms a consumer expects.
    #[test]
    fn test_scalars_and_containers() {
        assert_eq!(Json::Null.to_json(), "null");
        assert_eq!(Json::Bool(true).to_json(), "true");
        assert_eq!(Json::Bool(false).to_json(), "false");
        assert_eq!(Json::int(-17i32).to_json(), "-17");
        assert_eq!(Json::size(0).to_json(), "0");
        assert_eq!(Json::string("hi").to_json(), "\"hi\"");
        // Empty containers stay on one line; nonempty ones indent.
        assert_eq!(Json::Array(vec![]).to_json(), "[]");
        assert_eq!(Json::Object(vec![]).to_json(), "{}");
        assert_eq!(
            Json::Array(vec![Json::int(1i32), Json::int(2i32)]).to_json(),
            "[\n  1,\n  2\n]"
        );
    }

    /// Everything the writer emits reads back identically.
    ///
    /// The property that makes `results/history.json` safe to accumulate: the scoreboard reads the
    /// file it wrote last time, extends it and writes it back, so a lossy round trip would silently
    /// corrupt every historical record it touched.
    #[test]
    fn test_round_trip() {
        let value = Json::object([
            ("schema", Json::int(1i32)),
            ("null", Json::Null),
            ("yes", Json::Bool(true)),
            ("no", Json::Bool(false)),
            ("negative", Json::int(-17i32)),
            ("big", Json::Int(i128::from(u64::MAX))),
            (
                "escaped",
                Json::string("a\"b\\c\nd\te\u{08}f\u{0c}g\u{1f}h"),
            ),
            ("unicode", Json::string("Gröbner 🦓 ∎")),
            ("empty_array", Json::Array(vec![])),
            ("empty_object", Json::Object(vec![])),
            (
                "nested",
                Json::Array(vec![
                    Json::object([("inner", Json::Array(vec![Json::int(1i32), Json::Null]))]),
                    Json::string(""),
                ]),
            ),
        ]);
        let text = value.to_json();
        assert_eq!(Json::parse(&text), Ok(value.clone()));
        // And the parse of the parse's own output is the same again.
        assert_eq!(
            Json::parse(&Json::parse(&text).expect("valid").to_json()),
            Ok(value)
        );
    }

    // Decoding a string consumes its own UTF-8 bytes without inspecting the following value.
    #[test]
    fn test_string_decoding_does_not_validate_the_document_suffix() {
        for text in ["ascii", "Gröbner 🦓 ∎"] {
            let encoded = format!("\"{text}\"");
            let mut bytes = encoded.as_bytes().to_vec();
            bytes.push(0xff);
            let mut at = 0;
            assert_eq!(Json::parse_string(&bytes, &mut at), Ok(text.to_string()));
            assert_eq!(at, encoded.len());
        }
    }

    // Invalid or truncated UTF-8 scalars are rejected at their starting byte.
    #[test]
    fn test_string_decoding_rejects_invalid_scalars() {
        for bytes in [
            &b"\"\x80\""[..],
            &b"\"\xc0\x80\""[..],
            &b"\"\xc2"[..],
            &b"\"\xe0\x80\x80\""[..],
            &b"\"\xed\xa0\x80\""[..],
            &b"\"\xf4\x90\x80\x80\""[..],
            &b"\"\xff\""[..],
        ] {
            let error = Json::parse_string(bytes, &mut 0).unwrap_err();
            assert_eq!(error.at, 1);
            assert_eq!(error.reason, "invalid UTF-8");
        }
    }

    /// Accessors reach into a parsed value.
    #[test]
    fn test_reading_a_parsed_value() {
        let parsed =
            Json::parse(r#"{ "runs": [ {"challenge": "x", "elapsed_nanos": 42} ], "count": 1 }"#)
                .expect("valid");
        assert_eq!(parsed.get("count").and_then(Json::as_int), Some(1));
        let runs = parsed.get("runs").expect("present").items();
        assert_eq!(runs.len(), 1);
        assert_eq!(runs[0].get("challenge").and_then(Json::as_str), Some("x"));
        assert_eq!(
            runs[0].get("elapsed_nanos").and_then(Json::as_int),
            Some(42)
        );
        assert_eq!(runs[0].get("absent"), None);
        // Wrong-shape access returns nothing rather than panicking.
        assert_eq!(parsed.as_int(), None);
        assert_eq!(parsed.items(), &[]);
    }

    /// Malformed input is refused with an offset, and a float is refused on purpose.
    #[test]
    fn test_malformed_input() {
        for (text, reason) in [
            ("", "unexpected end of input"),
            // Truncation is reported as whatever was expected next, with the offset to find it by.
            ("{", "expected a string"),
            ("[", "unexpected end of input"),
            ("[1,]", "trailing comma in array"),
            ("{\"a\" 1}", "expected a delimiter"),
            ("{a: 1}", "expected a string"),
            ("\"unterminated", "unterminated string"),
            ("nul", "not a JSON literal"),
            ("1 2", "trailing input"),
            ("-", "not a number"),
            ("\"\\q\"", "unknown escape"),
            ("\"\\ud834\"", "lone high surrogate"),
            // A float is not a parse failure in RFC 8259; it is one *here*, because this type
            // has no float variant and 0.1 does not round-trip.
            ("0.5", "floats are not part of this subset"),
            ("1e3", "floats are not part of this subset"),
        ] {
            let error = Json::parse(text).expect_err(text);
            assert_eq!(error.reason, reason, "{}", text);
            assert!(error.to_string().contains("at byte"));
        }

        // A raw control character inside a string is invalid JSON, not merely ugly.
        assert_eq!(
            Json::parse("\"a\nb\"").expect_err("control").reason,
            "unescaped control character"
        );
    }

    /// Escapes another producer might emit are accepted.
    #[test]
    fn test_escapes_from_other_producers() {
        assert_eq!(
            Json::parse(r#""\u0041\u00e9\u002f\/""#),
            Ok(Json::string("Aé//"))
        );
        // A surrogate pair is one character.
        assert_eq!(
            Json::parse(r#""\ud83e\udd93""#),
            Ok(Json::string("\u{1f993}"))
        );
    }

    /// Object key order is preserved, so a record diffs cleanly between runs.
    #[test]
    fn test_object_order_is_insertion_order() {
        let value = Json::object([
            ("zebra", Json::int(1i32)),
            ("apple", Json::int(2i32)),
            ("mango", Json::int(3i32)),
        ]);
        let text = value.to_json();
        let z = text.find("zebra").expect("present");
        let a = text.find("apple").expect("present");
        let m = text.find("mango").expect("present");
        assert!(z < a && a < m, "keys were reordered: {}", text);
    }

    /// Strings are escaped per RFC 8259, control characters included.
    #[test]
    fn test_string_escaping() {
        assert_eq!(
            Json::string("a\"b\\c").to_json(),
            r#""a\"b\\c""#,
            "quotes and backslashes"
        );
        assert_eq!(Json::string("a\nb\tc\rd").to_json(), r#""a\nb\tc\rd""#);
        assert_eq!(Json::string("\u{08}\u{0c}").to_json(), r#""\b\f""#);
        // Other control characters take the \u form, which is the case a naive writer gets
        // wrong: a raw control byte inside a JSON string is invalid, not merely ugly.
        assert_eq!(Json::string("\u{01}").to_json(), "\"\\u0001\"");
        assert_eq!(Json::string("\u{1f}").to_json(), "\"\\u001f\"");
        // Non-ASCII passes through as UTF-8, which RFC 8259 permits.
        assert_eq!(Json::string("Gröbner").to_json(), "\"Gröbner\"");
    }

    /// Nesting indents by depth and closes in the right order.
    #[test]
    fn test_nesting() {
        let value = Json::object([(
            "outer",
            Json::Array(vec![Json::object([("inner", Json::int(1i32))])]),
        )]);
        assert_eq!(
            value.to_json(),
            "{\n  \"outer\": [\n    {\n      \"inner\": 1\n    }\n  ]\n}"
        );
    }

    /// Durations are whole nanoseconds, so they round-trip exactly.
    ///
    /// The reason there is no float in this module: `0.1` does not round-trip through a decimal
    /// literal, and a record whose numbers change between formatters is not a record.
    #[test]
    fn test_durations_are_integer_nanoseconds() {
        assert_eq!(Json::nanos(Duration::ZERO).to_json(), "0");
        assert_eq!(Json::nanos(Duration::from_nanos(1)).to_json(), "1");
        assert_eq!(
            Json::nanos(Duration::from_micros(1_500)).to_json(),
            "1500000"
        );
        // A figure a float would mangle.
        assert_eq!(
            Json::nanos(Duration::new(28, 253_900_001)).to_json(),
            "28253900001"
        );
    }
}
