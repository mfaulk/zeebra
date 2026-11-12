//! The engine parses and echoes the requested ring; solve timing excludes parsing and output.
use serde_json::{Value, json};
const REVISION: &str = "c3e1d630fba9b2155a4c389d9022f13e0ba09218";
fn identity() -> Value {
    json!({"contract":1,"revision":REVISION,"build":env!("GROEBNER_DRIVER_ID"),"build_metadata":env!("GROEBNER_DRIVER_BUILD"),
        "algorithm":"groebner_basis_f4(canonicalize=true); randomized modular row combinations",
        "allocator":"system", "features":"parallel; no mimalloc",
        "isa":if cfg!(all(target_feature="avx2",target_feature="bmi2",target_feature="fma")) {"x86-64-v3"} else {"other"}})
}
fn solve(input: &Value) -> Result<Value, String> {
    use groebner::{MonomialOrder, PolynomialRing, Zp, groebner_basis_f4};
    let start = std::time::Instant::now();
    let variables: Vec<String> = input["variables"]
        .as_array()
        .ok_or("variables must be an array")?
        .iter()
        .map(|v| {
            v.as_str()
                .map(str::to_owned)
                .ok_or("variable must be a string")
        })
        .collect::<Result<_, _>>()?;
    let modulus = input["modulus"].as_u64().ok_or("modulus must be u64")?;
    if modulus < 2 {
        return Err("modulus must be a prime >= 2".into());
    }
    let order_tag = input["order"].as_str().ok_or("missing order")?;
    let order = match order_tag {
        "grevlex" => MonomialOrder::GRevLex,
        "grlex" => MonomialOrder::GrLex,
        "lex" => MonomialOrder::Lex,
        _ => return Err("unsupported order".into()),
    };
    let workers = input["workers"]
        .as_u64()
        .filter(|n| *n > 0 && *n <= 1024)
        .ok_or("invalid worker count")? as usize;
    let ring = PolynomialRing::<Zp>::with_modulus(variables.clone(), order, modulus)
        .map_err(|e| e.to_string())?;
    let generators = input["generators"]
        .as_array()
        .ok_or("missing generators")?
        .iter()
        .map(|v| {
            ring.parse(v.as_str().ok_or("generator must be a string")?)
                .map_err(|e| e.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let echoed = generators
        .iter()
        .map(|p| ring.format(p).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .map_err(|e| e.to_string())?;
    let parse_ns = start.elapsed().as_nanos() as u64;
    let start = std::time::Instant::now();
    let (basis, actual_workers) = pool.install(|| {
        (
            groebner_basis_f4(generators, true),
            rayon::current_num_threads(),
        )
    });
    let basis = basis.map_err(|e| e.to_string())?;
    let solve_ns = start.elapsed().as_nanos() as u64;
    let start = std::time::Instant::now();
    let rendered = basis
        .iter()
        .map(|p| ring.format(p).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    let leading = basis
        .iter()
        .filter_map(|p| p.terms.first())
        .map(|t| ring.format_monomial(&t.0).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    let mut result = identity();
    result["variables"] = json!(ring.variables());
    result["modulus"] = json!(ring.modulus());
    result["order"] = json!(match ring.order() {
        MonomialOrder::GRevLex => "grevlex",
        MonomialOrder::GrLex => "grlex",
        MonomialOrder::Lex => "lex",
        _ => return Err("engine returned an unexpected ring order".into()),
    });
    result["workers"] = json!(actual_workers);
    result["generators"] = json!(echoed);
    result["basis"] = json!(rendered);
    result["leading"] = json!(leading);
    result["parse_ns"] = json!(parse_ns);
    result["solve_ns"] = json!(solve_ns);
    // Includes rendering and a full JSON encoding; stdout transfer remains process wall time.
    let _ = serde_json::to_vec(&result).map_err(|e| e.to_string())?;
    result["serialization_ns"] = json!(start.elapsed().as_nanos() as u64);
    Ok(result)
}
fn main() -> Result<(), String> {
    let arg = std::env::args()
        .nth(1)
        .ok_or("expected input path or --version")?;
    let result = if arg == "--version" || arg == "--startup" {
        identity()
    } else {
        let text = std::fs::read_to_string(arg).map_err(|e| e.to_string())?;
        solve(&serde_json::from_str(&text).map_err(|e| e.to_string())?)?
    };
    println!(
        "{}",
        serde_json::to_string(&result).map_err(|e| e.to_string())?
    );
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    // The engine preserves ordered variable names and full unsigned 64-bit residues.
    #[test]
    fn echoes_the_engine_ring_at_wide_moduli() {
        let input = json!({"variables":["x10","x1"],"modulus":18446744073709551263u64,
            "order":"grevlex","workers":1,"generators":["x10 + 18446744073709551262*x1", "x1^2-1"]});
        let output = solve(&input).unwrap();
        assert_eq!(output["variables"], input["variables"]);
        assert_eq!(output["modulus"], input["modulus"]);
        assert_eq!(output["workers"], 1);
        assert_eq!(output["basis"].as_array().unwrap().len(), 2);
        assert!(output["generators"][0].as_str().unwrap().contains("x10"));
    }
    // Unknown variables and unsupported monomial orders are refused before computation.
    #[test]
    fn rejects_invalid_input() {
        for order in ["grevlex", "weighted"] {
            assert!(
                solve(&json!({"variables":["x"],"modulus":32003,
                "order":order,"workers":1,"generators":["z-1"]}))
                .is_err()
            );
        }
    }
}
