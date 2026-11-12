use serde_json::{Value, json};
use std::time::{Duration, Instant};
use sylvester::{
    Backend, Budget, CertifyError, ComputeOptions, Polynomial, PolynomialRing, PrimeField, verify,
};
const REVISION: &str = "ea34ddf3c9b9a275265576cd881c39c0c473e9f9";
fn identity() -> Value {
    json!({"contract":1,"revision":REVISION,"version":"0.4.0","build":env!("SYLVESTER_DRIVER_ID"),"build_metadata":env!("SYLVESTER_DRIVER_BUILD"),"allocator":"system","isa":if cfg!(all(target_feature="avx2",target_feature="bmi2",target_feature="fma")){"x86-64-v3"}else{"other"}})
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
fn parsed(
    input: &Value,
) -> Result<(PolynomialRing<PrimeField>, Vec<Polynomial<PrimeField>>), String> {
    let variables = strings(input, "variables")?;
    let p = input["modulus"].as_u64().ok_or("missing modulus")?;
    let ring = PolynomialRing::prime_field(p, &variables).map_err(|e| e.to_string())?;
    let generators = strings(input, "generators")?
        .iter()
        .map(|g| ring.parse_polynomial(g).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((ring, generators))
}
fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
#[cfg(test)]
fn decode_hex(text: &str) -> Result<Vec<u8>, String> {
    if !text.len().is_multiple_of(2) {
        return Err("odd hex length".into());
    }
    text.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            std::str::from_utf8(pair)
                .ok()
                .and_then(|s| u8::from_str_radix(s, 16).ok())
                .ok_or_else(|| "invalid hex".into())
        })
        .collect()
}
fn engine_terms(poly: &Polynomial<PrimeField>) -> Vec<(u64, Vec<u32>)> {
    poly.terms()
        .map(|(c, m)| (c.value(), m.iter().map(|n| *n as u32).collect()))
        .collect()
}
fn verifier_terms(poly: &verify::Poly) -> Vec<(u64, Vec<u32>)> {
    poly.terms()
        .iter()
        .map(|t| (t.coeff(), t.mono().exps().to_vec()))
        .collect()
}
fn bind_certificate(bytes: &[u8], input: &Value) -> Result<verify::VerifiedGb, String> {
    let limits = verify::Limits {
        deadline: Some(
            Instant::now()
                + Duration::from_nanos(input["wall_ns"].as_u64().ok_or("missing deadline")?),
        ),
        ..verify::Limits::default()
    };
    let checked = verify::v2::verify_with_limits(bytes, &limits).map_err(|e| {
        if e.is_exhaustion() {
            format!("exhausted:{e}")
        } else {
            format!("rejected:{e}")
        }
    })?;
    let (ring, polys) = parsed(input)?;
    if checked.modulus() != ring.modulus()
        || checked.nvars() != ring.nvars()
        || checked
            .input()
            .iter()
            .map(verifier_terms)
            .collect::<Vec<_>>()
            != polys.iter().map(engine_terms).collect::<Vec<_>>()
    {
        return Err("certificate describes a different input".into());
    }
    Ok(checked)
}
fn solve(input: &Value) -> Result<Value, String> {
    let start = Instant::now();
    if input["order"].as_str() != Some("grevlex") {
        return Err("only grevlex F4 is supported".into());
    }
    let mode = input["mode"].as_str().ok_or("missing objective")?;
    if !matches!(mode, "raw" | "certified") {
        return Err("unknown objective".into());
    }
    let workers = input["workers"]
        .as_u64()
        .filter(|n| *n > 0 && *n <= 1024)
        .ok_or("invalid worker count")? as usize;
    if mode == "certified" && workers != 1 {
        return Err("trace recording is serial".into());
    }
    let (ring, generators) = parsed(input)?;
    let echo = generators
        .iter()
        .map(|p| format!("[{p}]:\n"))
        .collect::<Vec<_>>();
    let ideal = ring.ideal(generators).map_err(|e| e.to_string())?;
    let wall = Duration::from_nanos(input["wall_ns"].as_u64().ok_or("missing deadline")?);
    let mut budget = Budget::new().timeout(wall);
    if let Some(bytes) = input["rss_bytes"].as_u64() {
        budget = budget
            .memory_limit(usize::try_from(bytes).map_err(|_| "memory cap does not fit usize")?);
    }
    let options = ComputeOptions::new()
        .backend(Backend::F4)
        .threads(workers)
        .budget(budget);
    let parse_ns = start.elapsed().as_nanos() as u64;
    let mut output = identity();
    output["input"] = input.clone();
    output["generator_echoes"] = json!(echo);
    output["basis"] = Value::Null;
    output["certificate"] = Value::Null;
    output["certified"] = Value::Null;
    output["stopped"] = Value::Null;
    output["parse_ns"] = json!(parse_ns);
    output["backend"] = json!("f4");
    output["parsed_variables"] = json!(ring.variables());
    output["parsed_modulus"] = json!(ring.modulus());
    let start = Instant::now();
    type Computed = (Vec<String>, usize, Option<Vec<u8>>, u64);
    let outcome: Result<Computed, String> = if mode == "raw" {
        match ideal.groebner_basis_with_report(options) {
            Ok((basis, report)) => {
                if report.backend != Backend::F4 {
                    return Err("backend substituted".into());
                }
                Ok((
                    basis.iter().map(ToString::to_string).collect(),
                    report.threads_used,
                    None,
                    report.elapsed.as_nanos() as u64,
                ))
            }
            Err(e) => Err(format!("engine:{e:?}")),
        }
    } else {
        match ideal.groebner_basis_certified(options) {
            Ok(certified) => Ok((
                certified.basis().iter().map(ToString::to_string).collect(),
                1,
                Some(certified.certificate().to_vec()),
                start.elapsed().as_nanos() as u64,
            )),
            Err(CertifyError::Engine(e) | CertifyError::WriterExhausted(e)) => {
                Err(format!("engine:{e:?}"))
            }
            Err(CertifyError::VerifierExhausted(e)) => Err(format!("exhausted:{e}")),
            Err(CertifyError::CapExceeded { cap, limit }) => {
                Err(format!("exhausted:{cap:?}:{limit}"))
            }
            Err(e) => return Err(format!("certificate rejected: {e}")),
        }
    };
    let total_ns = start.elapsed().as_nanos() as u64;
    match outcome {
        Ok((basis, actual, certificate, engine_ns)) => {
            let mut bind_ns = 0;
            if let Some(bytes) = certificate {
                let verify_start = Instant::now();
                let checked = match bind_certificate(&bytes, input) {
                    Ok(v) => v,
                    Err(e) if e.starts_with("exhausted:") => {
                        output["stopped"] = json!(e);
                        return Ok(output);
                    }
                    Err(e) => return Err(e),
                };
                bind_ns = verify_start.elapsed().as_nanos() as u64;
                let expected = basis
                    .iter()
                    .map(|p| {
                        ring.parse_polynomial(p)
                            .map(|p| engine_terms(&p))
                            .map_err(|e| e.to_string())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if checked
                    .basis()
                    .iter()
                    .map(verifier_terms)
                    .collect::<Vec<_>>()
                    != expected
                {
                    return Err("certificate basis differs from result".into());
                }
                output["certificate"] = json!(encode_hex(&bytes));
                output["certificate_bytes"] = json!(bytes.len());
                output["certified"] = json!(true);
            }
            output["basis_count"] = json!(basis.len());
            output["basis"] = json!(format!("[{}]:\n", basis.join(",\n")));
            output["solve_ns"] = json!(total_ns + bind_ns);
            output["engine_ns"] = json!(engine_ns);
            output["binding_verify_ns"] = json!(bind_ns);
            output["actual_workers"] = json!(actual);
            output["complete"] = json!(true);
            output["certificate_format"] = if mode == "certified" {
                json!("sylv-gb-cert-v2")
            } else {
                Value::Null
            };
            output["solve_ns"] = json!(start.elapsed().as_nanos() as u64);
        }
        Err(message) if message.starts_with("exhausted:") || message.starts_with("engine:") => {
            output["stopped"] = json!(message);
        }
        Err(message) => return Err(message),
    }
    Ok(output)
}
fn main() -> Result<(), String> {
    let arg = std::env::args()
        .nth(1)
        .ok_or("expected input path, --startup or --version")?;
    let mut output = if arg == "--version" || arg == "--startup" {
        identity()
    } else {
        let bytes = std::fs::read(arg).map_err(|e| e.to_string())?;
        if bytes.len() > 8 * 1024 * 1024 {
            return Err("request exceeds 8 MiB".into());
        }
        solve(&serde_json::from_slice(&bytes).map_err(|e| e.to_string())?)?
    };
    std::hint::black_box(serde_json::to_vec(&output).map_err(|e| e.to_string())?);
    output["kernel_peak_rss_bytes"] = json!(peak_rss());
    println!(
        "{}",
        serde_json::to_string(&output).map_err(|e| e.to_string())?
    );
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn input(generators: Vec<&str>, p: u64, mode: &str) -> Value {
        json!({"variables":["x","y","z"],"modulus":p,"order":"grevlex","workers":1,"mode":mode,"wall_ns":10000000000u64,"rss_bytes":1073741824u64,"generators":generators})
    }
    // The pinned F4 fixes both independently documented historical wrong-ideal and non-basis cases.
    #[test]
    fn repairs_known_counterexamples() {
        for mode in ["raw", "certified"] {
            let a = solve(&input(vec!["x^3+y^3", "x+x^2+x^2*y", "y+x^2"], 2, mode)).unwrap();
            let basis = a["basis"].as_str().unwrap();
            assert!(basis.contains('x') && basis.contains('y'));
            assert!(!basis.contains('^'));
            let b = solve(&input(vec!["x^2+y^2", "x*z+x*y", "y+x*y"], 3, mode)).unwrap();
            assert_eq!(b["basis_count"], 5);
            if mode == "certified" {
                assert_eq!(a["certified"], true);
                assert_eq!(b["certified"], true);
            }
        }
    }
    // Zero, unit, nonradical and positive-dimensional ideals keep exact input identity and certificates.
    #[test]
    fn binds_exact_certificates() {
        for generators in [
            vec!["0"],
            vec!["x", "x-1"],
            vec!["x^2", "y^2"],
            vec!["0", "x*y", "x*y"],
        ] {
            let request = input(generators, 32003, "certified");
            let output = solve(&request).unwrap();
            assert_eq!(output["input"], request);
            assert_eq!(output["certified"], true);
            let bytes = decode_hex(output["certificate"].as_str().unwrap()).unwrap();
            assert!(bind_certificate(&bytes, &request).is_ok());
            let mut wrong = request.clone();
            wrong["generators"] = json!(["1"]);
            assert!(bind_certificate(&bytes, &wrong).is_err());
            wrong = request.clone();
            wrong["modulus"] = json!(7);
            assert!(bind_certificate(&bytes, &wrong).is_err());
            let mut tampered = bytes;
            tampered[0] ^= 1;
            assert!(bind_certificate(&tampered, &request).is_err());
        }
    }
    // Unsupported field/order/certified-worker combinations fail before silently changing the backend.
    #[test]
    fn refuses_unsupported_requests() {
        let base = input(vec!["x"], 32003, "raw");
        for (key, value) in [
            ("order", json!("lex")),
            ("modulus", json!(18446744073709551557u64)),
            ("mode", json!("cheap")),
        ] {
            let mut request = base.clone();
            request[key] = value;
            assert!(solve(&request).is_err());
        }
        let mut request = base;
        request["mode"] = json!("certified");
        request["workers"] = json!(4);
        assert!(solve(&request).is_err());
    }
    // Internal deadline exhaustion produces a typed stop without a basis or certification claim.
    #[test]
    fn reports_exhaustion() {
        let mut request = input(vec!["x^2+y", "x*y-1"], 32003, "certified");
        request["wall_ns"] = json!(0);
        let output = solve(&request).unwrap();
        assert!(output["stopped"].is_string());
        assert!(output["basis"].is_null());
        assert!(output["certified"].is_null());
    }
}
