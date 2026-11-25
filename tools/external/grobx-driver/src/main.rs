use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    num::NonZeroUsize,
    time::{Duration, Instant},
};
const REVISION: &str = "8005a2a1670a7264617a6f49eeb2618d7fa21701";
#[global_allocator]
static GLOBAL: grobx::Allocator = grobx::Allocator;
fn identity() -> Value {
    json!({"contract":1,"revision":REVISION,"version":grobx::VERSION,
        "build":env!("GROBX_DRIVER_ID"),"build_metadata":env!("GROBX_DRIVER_BUILD"),
        "allocator":"grobx::Allocator (mimalloc small blocks; system large blocks)",
        "isa":if cfg!(all(target_feature="avx2",target_feature="bmi2",target_feature="fma")){"x86-64-v3"}else{"other"}})
}
fn peak_rss() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find_map(|s| {
            s.strip_prefix("VmHWM:")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()?
                .checked_mul(1024)
        })
}
fn strings(input: &Value, key: &str) -> Result<Vec<String>, String> {
    input[key]
        .as_array()
        .ok_or_else(|| format!("missing {key}"))?
        .iter()
        .map(|v| {
            v.as_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("invalid {key}"))
        })
        .collect()
}
// `m33-basis-v1`, ported from `tools/external/basis_digest.py` (its `canonical_polynomial` and
// `digest_canonical`, over the elements `research/m33-baseline/admission.py::grobx_digest` splits
// out of a reply), so a digest-only reply is compared with the reference as a full one is.
fn basis_m33(text: &str, modulus: u64, variables: &[String]) -> Result<String, String> {
    let p = u128::from(modulus);
    let mul = |a: u128, b: u128| a * b % p;
    let pow = |mut b: u128, mut e: u64| {
        let mut r = 1 % p;
        while e > 0 {
            if e & 1 == 1 {
                r = mul(r, b);
            }
            b = mul(b, b);
            e >>= 1;
        }
        r
    };
    let index: std::collections::HashMap<&str, usize> = variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.as_str(), i))
        .collect();
    let mut elements = Vec::new();
    for element in text.split([',', '\n', '[', ']', ':']) {
        if element.trim().is_empty() {
            continue;
        }
        let compact: String = element.split_whitespace().collect();
        let mut terms = std::collections::BTreeMap::<Vec<u64>, u128>::new();
        for term in compact.replace('-', "+-").split('+') {
            if term.is_empty() {
                continue;
            }
            let mut coefficient = if term.starts_with('-') { p - 1 } else { 1 };
            let mut exponents = vec![0u64; variables.len()];
            for factor in term.trim_start_matches('-').split('*') {
                let invalid = || format!("invalid polynomial factor: {factor}");
                let (base, power) = match factor.split_once('^') {
                    Some((b, e)) if !e.is_empty() && e.bytes().all(|c| c.is_ascii_digit()) => {
                        (b, e.parse::<u64>().map_err(|_| invalid())?)
                    }
                    Some(_) => return Err(invalid()),
                    None => (factor, 1),
                };
                if !base.is_empty() && base.bytes().all(|c| c.is_ascii_digit()) {
                    let value = base
                        .bytes()
                        .fold(0, |v, d| (v * 10 + u128::from(d - b'0')) % p);
                    coefficient = mul(coefficient, pow(value, power));
                } else if base.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
                    && base.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_')
                {
                    let i = *index
                        .get(base)
                        .ok_or_else(|| format!("unknown polynomial variable: {base}"))?;
                    exponents[i] = exponents[i].checked_add(power).ok_or_else(invalid)?;
                } else {
                    return Err(invalid());
                }
            }
            let sum = terms.entry(exponents).or_insert(0);
            *sum = (*sum + coefficient) % p;
        }
        terms.retain(|_, c| *c != 0);
        let Some(leading) = terms.iter().max_by(|a, b| {
            let degree = |m: &[u64]| m.iter().map(|&e| u128::from(e)).sum::<u128>();
            degree(a.0)
                .cmp(&degree(b.0))
                .then_with(|| b.0.iter().rev().cmp(a.0.iter().rev()))
        }) else {
            continue;
        };
        // The leading coefficient's inverse by the extended Euclidean algorithm, as Python's
        // `pow(c, -1, p)`; a reduced basis over a prime field always has one.
        let (mut r0, mut r1, mut t0, mut t1) = (p as i128, *leading.1 as i128, 0i128, 1i128);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (t0, t1) = (t1, t0 - q * t1);
        }
        if r0 != 1 {
            return Err("leading coefficient has no inverse".into());
        }
        let scale = t0.rem_euclid(p as i128) as u128;
        let mut bytes = Vec::new();
        for (monomial, c) in &terms {
            for &e in monomial {
                let mut e = e;
                while e >= 0x80 {
                    bytes.push((e as u8 & 0x7f) | 0x80);
                    e >>= 7;
                }
                bytes.push(e as u8);
            }
            bytes.extend_from_slice(format!("{};", mul(*c, scale)).as_bytes());
        }
        elements.push(bytes);
    }
    elements.sort_unstable();
    let mut hasher = Sha256::new();
    hasher.update(format!("m33-basis-v1 {modulus} {}\n", variables.len()).as_bytes());
    for element in &elements {
        hasher.update((element.len() as u32).to_le_bytes());
        hasher.update(element);
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect())
}
fn solve(input: &Value) -> Result<Value, String> {
    let start = Instant::now();
    let variables = strings(input, "variables")?;
    if variables.is_empty()
        || variables.len() > 128
        || variables.iter().any(|v| {
            v.is_empty()
                || !v.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                || v.as_bytes()[0].is_ascii_digit()
        })
    {
        return Err("invalid ordered variables".into());
    }
    let modulus = input["modulus"]
        .as_u64()
        .filter(|p| *p >= 2)
        .ok_or("invalid modulus")?;
    let generators = strings(input, "generators")?;
    if generators
        .iter()
        .any(|g| g.contains([',', '\n', '\r', '[', ']', ':']))
    {
        return Err("invalid generator separators".into());
    }
    let order = match input["order"].as_str() {
        Some("grevlex") => grobx::MonomialOrder::Grevlex,
        Some("lex") => grobx::MonomialOrder::Lex,
        _ => return Err("unsupported order".into()),
    };
    // #1127: `Block(vec![1; n - 1])` is exactly lex (one variable per block), and grobx runs a
    // block order by F4 in that order: no grevlex run, no FGLM.
    let lex_route = match input.get("lex_route") {
        None => "auto",
        Some(v) => match v.as_str() {
            Some("auto") => "auto",
            Some("f4") if order == grobx::MonomialOrder::Lex && variables.len() > 1 => "f4",
            Some("f4") => {
                return Err("lex_route f4 needs order lex and two or more variables".into());
            }
            _ => return Err("invalid lex_route".into()),
        },
    };
    let order = if lex_route == "f4" {
        grobx::MonomialOrder::Block(vec![1; variables.len() - 1])
    } else {
        order
    };
    let grobx_order = order.to_string();
    // A multi-worker request is refused unless it is #966's thread probe, which asks the library
    // for `workers` threads to observe how many it computes on; no timing row uses it.
    let workers = input["workers"].as_u64().unwrap_or(0) as usize;
    let probe = input["threads_probe"].as_bool() == Some(true);
    if workers != 1 && !(probe && workers > 1) {
        return Err("this revision computes on one thread".into());
    }
    let mode = input["mode"].as_str().ok_or("missing mode")?;
    let digest_only = match input.get("digest_only") {
        None => false,
        Some(v) => v.as_bool().ok_or("invalid digest_only")?,
    };
    if !matches!(mode, "raw" | "certified") {
        return Err("unsupported objective".into());
    }
    let header = format!("{}\n{modulus}\n", variables.join(","));
    let mut engine_echo = Vec::new();
    let mut checker_echo = Vec::new();
    for generator in &generators {
        let text = format!("{header}{generator}\n");
        engine_echo.push(grobx::text::generators(&text).map_err(|e| e.to_string())?);
        checker_echo.push(grobx_checker::generators(&text).map_err(|e| format!("{e:?}"))?);
    }
    if engine_echo != checker_echo {
        return Err("independent parsers disagree".into());
    }
    let text = format!(
        "{header}{}\n",
        if generators.is_empty() {
            "0".into()
        } else {
            generators.join(",\n")
        }
    );
    let mut params = grobx::Params::new(
        order,
        grobx::Threads::Count(NonZeroUsize::new(workers).unwrap()),
        0,
    );
    params.report = true;
    params.deadline = Some(Duration::from_nanos(
        input["wall_ns"].as_u64().ok_or("missing deadline")?,
    ));
    params.memory = input["rss_bytes"].as_u64();
    if mode == "certified" {
        params.checker = Some(grobx::CheckerMode::Exact);
        params.cofactors = true;
    }
    let parse_ns = start.elapsed().as_nanos() as u64;
    let start = Instant::now();
    let outcome = grobx::groebner(&text, &params).map_err(|e| e.to_string())?;
    let solve_ns = start.elapsed().as_nanos() as u64;
    let mut output = identity();
    output["input"] = input.clone();
    output["input_text"] = json!(text);
    output["input_sha256"] = json!(grobx::digest(&text));
    output["lex_route"] = json!(lex_route);
    output["grobx_order"] = json!(grobx_order);
    output["generator_echoes"] = json!(engine_echo);
    output["checker_echoes"] = json!(checker_echo);
    if digest_only {
        // #1020: Eco-12's certified texts gzip to 1.7 GB, past the journal's output budget.
        let start = Instant::now();
        let digest = match &outcome.basis {
            Some(basis) => Some(basis_m33(basis, modulus, &variables)?),
            None => None,
        };
        output["basis_m33"] = json!(digest);
        output["basis_m33_ns"] = json!(start.elapsed().as_nanos() as u64);
        output["basis_bytes"] = json!(outcome.basis.as_ref().map(String::len));
        output["cofactors_bytes"] = json!(outcome.cofactors.as_ref().map(String::len));
        output["basis"] = Value::Null;
        output["cofactors"] = Value::Null;
    } else {
        output["basis"] = json!(outcome.basis);
        output["cofactors"] = json!(outcome.cofactors);
    }
    output["certified"] = json!(outcome.certified);
    output["flaw"] = json!(outcome.flaw);
    output["stopped"] = json!(outcome.stopped.map(|s| s.name()));
    output["report"] = json!(outcome.report);
    output["parse_ns"] = json!(parse_ns);
    output["solve_ns"] = json!(solve_ns);
    output["kernel_peak_rss_bytes"] = json!(peak_rss());
    Ok(output)
}
fn main() -> Result<(), String> {
    let arg = std::env::args()
        .nth(1)
        .ok_or("expected input path, --startup or --version")?;
    let mut result = if arg == "--version" || arg == "--startup" {
        identity()
    } else {
        let text = std::fs::read_to_string(arg).map_err(|e| e.to_string())?;
        if text.len() > 8 * 1024 * 1024 {
            return Err("input exceeds the 8 MiB driver limit".into());
        }
        solve(&serde_json::from_str(&text).map_err(|e| e.to_string())?)?
    };
    std::hint::black_box(serde_json::to_vec(&result).map_err(|e| e.to_string())?);
    result["kernel_peak_rss_bytes"] = json!(peak_rss());
    println!(
        "{}",
        serde_json::to_string(&result).map_err(|e| e.to_string())?
    );
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    // The independent parsers preserve generator positions, prefixes, zeroes and wide residues.
    #[test]
    fn parses_ordered_wide_generators() {
        let p = 18_446_744_073_709_551_557u64;
        let input = json!({"variables":["x10","x1"],"modulus":p,"order":"grevlex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":["2*x10-2*x1","0","x1^2-1","x1^2-1"]});
        let output = solve(&input).unwrap();
        assert_eq!(output["input"], input);
        assert_eq!(output["generator_echoes"].as_array().unwrap().len(), 4);
        assert_eq!(output["generator_echoes"][1], "[]:\n");
        assert_eq!(output["generator_echoes"], output["checker_echoes"]);
        assert!(output["basis"].as_str().unwrap().ends_with(":\n"));
        assert!(
            output["report"]
                .as_str()
                .unwrap()
                .contains("characteristic=18446744073709551557")
        );
    }
    // Exact certification requires a successful independent checker and returns the certificate data.
    #[test]
    fn certifies_nonradical_and_unit_ideals() {
        for generators in [vec!["x^2"], vec!["x", "x-1"], vec!["0"]] {
            let output=solve(&json!({"variables":["x"],"modulus":32003,"order":"grevlex","workers":1,
                "mode":"certified","wall_ns":10000000000u64,"rss_bytes":1073741824u64,"generators":generators})).unwrap();
            assert_eq!(output["certified"], true);
            assert!(output["cofactors"].is_string());
        }
    }
    // Unsupported objectives and worker requests fail rather than silently changing the computation.
    #[test]
    fn refuses_bad_parameters() {
        let base = json!({"variables":["x"],"modulus":32003,"order":"grevlex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,"generators":["x"]});
        for (key, value) in [
            ("workers", json!(4)),
            ("order", json!("grlex")),
            ("mode", json!("cheap")),
            ("modulus", json!(15)),
            ("generators", json!(["z"])),
        ] {
            let mut input = base.clone();
            input[key] = value;
            assert!(solve(&input).is_err(), "{key}");
        }
        let mut probe = base.clone();
        probe["workers"] = json!(16);
        probe["threads_probe"] = json!(true);
        assert!(solve(&probe).is_ok(), "the thread probe is accepted");
    }
    // The digest equals `basis_digest.py`'s on grobx's manual example, the unit and the zero ideal.
    #[test]
    fn basis_digest_matches_the_python_digest() {
        let xy = ["x".to_string(), "y".to_string()];
        assert_eq!(
            basis_m33("[y^2+x,\nx*y+6,\nx^2+y]:\n", 7, &xy).unwrap(),
            "d9920af7738a99cecec9464694df0e803b22f1abbee0358091a635d263ade3cf"
        );
        let x12 = ["x1".to_string(), "x2".to_string()];
        let shared = "8fb196a0f7de4f7d36d2d8c6b34fb80eebd5f04658fcc799e1f2583781e5fefc";
        for text in [
            "[2*x1*x2+4,\nx2^2+32002,\nx1^2+3*x2]:\n",
            "[1*x1^2+3*x2^1,x2^2-1,x1*x2+2]",
        ] {
            assert_eq!(basis_m33(text, 32003, &x12).unwrap(), shared);
        }
        let x = ["x".to_string()];
        assert_eq!(
            basis_m33("[1]:\n", 32003, &x).unwrap(),
            "353bd285ccd03dbd555af7ac297f05056ad28d6b1f297679e8118bcaf7044eb6"
        );
        assert_eq!(
            basis_m33("[]:\n", 32003, &x).unwrap(),
            "862b98973014a66352e21298112d0faa088fc9470804751af9f004147fee8410"
        );
        assert!(basis_m33("[z]:\n", 32003, &x).is_err());
    }
    // A digest-only certified reply drops the basis and cofactor texts and carries the full reply's digest.
    #[test]
    fn digest_only_reply_carries_the_full_replys_digest() {
        let mut input = json!({"variables":["x","y","z"],"modulus":32003,"order":"grevlex","workers":1,
            "mode":"certified","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":["x+y+z","x*y+y*z+z*x","x*y*z-1"]});
        let full = solve(&input).unwrap();
        let variables = strings(&input, "variables").unwrap();
        let expected = basis_m33(full["basis"].as_str().unwrap(), 32003, &variables).unwrap();
        assert!(full.get("basis_m33").is_none(), "a full reply is unchanged");
        input["digest_only"] = json!(true);
        let digest = solve(&input).unwrap();
        assert_eq!(digest["basis_m33"], expected);
        assert_eq!(digest["certified"], true);
        assert!(digest["basis"].is_null() && digest["cofactors"].is_null());
        assert_eq!(digest["basis_bytes"], full["basis"].as_str().unwrap().len());
        input["digest_only"] = json!("yes");
        assert!(solve(&input).is_err());
    }
    // #1127: `lex_route: "f4"` runs F4 in the exact-lex block order, so it skips FGLM and returns
    // the same lex basis as the default route.
    #[test]
    fn forced_f4_lex_route_skips_fglm_and_returns_the_lex_basis() {
        let mut input = json!({"variables":["x","y","z"],"modulus":32003,"order":"lex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":["x^2+y*z-3","y^2-x*z+z","z^3+x*y-2"]});
        let variables = strings(&input, "variables").unwrap();
        let auto = solve(&input).unwrap();
        let auto_report = auto["report"].as_str().unwrap();
        assert!(
            auto_report.contains(" fglm "),
            "the default route is FGLM: {auto_report}"
        );
        assert_eq!(auto["lex_route"], "auto");
        input["lex_route"] = json!("f4");
        let forced = solve(&input).unwrap();
        let report = forced["report"].as_str().unwrap();
        assert!(!report.contains(" fglm "), "{report}");
        assert!(report.contains("order=block"), "{report}");
        assert!(
            !report.contains("order=grevlex"),
            "no grevlex prelude: {report}"
        );
        assert_eq!(forced["lex_route"], "f4");
        assert_eq!(forced["grobx_order"], "block:1,1");
        assert_eq!(
            basis_m33(forced["basis"].as_str().unwrap(), 32003, &variables).unwrap(),
            basis_m33(auto["basis"].as_str().unwrap(), 32003, &variables).unwrap()
        );
        input["mode"] = json!("certified");
        assert_eq!(solve(&input).unwrap()["certified"], true);
    }
    // A forced route is refused where it cannot mean F4 in lex.
    #[test]
    fn refuses_a_forced_route_it_cannot_honour() {
        let base = json!({"variables":["x","y"],"modulus":32003,"order":"lex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":["x^2-y","y^2-1"],"lex_route":"f4"});
        assert!(solve(&base).is_ok());
        for (key, value) in [
            ("order", json!("grevlex")),
            ("lex_route", json!("fglm")),
            ("lex_route", json!(1)),
            ("variables", json!(["x"])),
        ] {
            let mut input = base.clone();
            input[key] = value;
            if key == "variables" {
                input["generators"] = json!(["x^2-1"]);
            }
            assert!(solve(&input).is_err(), "{key}={}", input[key]);
        }
    }
    // An exhausted internal budget returns a stop with no usable answer or certification.
    #[test]
    fn reports_stops_without_success() {
        let result = solve(
            &json!({"variables":["x"],"modulus":32003,"order":"grevlex","workers":1,
            "mode":"certified","wall_ns":0,"rss_bytes":1073741824u64,"generators":["x^2"]}),
        )
        .unwrap();
        assert!(result["stopped"].is_string());
        assert!(result["certified"].is_null());
        assert!(result["basis"].is_null());
    }
}
