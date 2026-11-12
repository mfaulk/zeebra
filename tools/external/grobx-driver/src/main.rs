use serde_json::{Value, json};
use std::{
    num::NonZeroUsize,
    time::{Duration, Instant},
};
const REVISION: &str = "1854835dbc25f24dc9a9ba017024d5030e99da1c";
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
    if input["workers"].as_u64() != Some(1) {
        return Err("this revision computes on one thread".into());
    }
    let mode = input["mode"].as_str().ok_or("missing mode")?;
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
        grobx::Threads::Count(NonZeroUsize::new(1).unwrap()),
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
    output["generator_echoes"] = json!(engine_echo);
    output["checker_echoes"] = json!(checker_echo);
    output["basis"] = json!(outcome.basis);
    output["cofactors"] = json!(outcome.cofactors);
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
