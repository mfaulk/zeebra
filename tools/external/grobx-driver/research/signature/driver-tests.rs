#[cfg(test)]
mod signature_contract_tests {
    use super::*;
    fn input(generators: &[&str], variables: &[&str], modulus: u64) -> Value {
        json!({"variables":variables,"modulus":modulus,"order":"grevlex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":generators})
    }
    fn cases() -> Vec<Value> {
        let katsura = [
            "x0+2*x1+2*x2+2*x3-1",
            "x0^2+2*x1^2+2*x2^2+2*x3^2-x0",
            "2*x0*x1+2*x1*x2+2*x2*x3-x1",
            "x1^2+2*x0*x2+2*x1*x3-x2",
        ];
        let mut out = Vec::new();
        for modulus in [32003u64, 2147483647, 18446744073709551263] {
            out.push(input(&["x^2+y^2-1", "x*y-1"], &["x", "y"], modulus));
            out.push(input(&katsura, &["x0", "x1", "x2", "x3"], modulus));
        }
        out
    }
    // Disabling handover keeps the signature engine to the end and returns the same complete basis.
    #[test]
    fn handover_off_preserves_the_basis_and_never_hands_over() {
        for base in cases() {
            let baseline = solve(&base).unwrap()["basis"].clone();
            for policy in ["native", "none"] {
                for handover in [true, false] {
                    let mut request = base.clone();
                    request["research_policy"] = json!(policy);
                    request["research_handover"] = json!(handover);
                    let result = solve(&request).unwrap();
                    assert_eq!(result["basis"], baseline);
                    assert_eq!(result["research_signature"]["handover"], json!(handover));
                    let report = result["report"].as_str().unwrap();
                    if !handover {
                        assert!(!report.contains("engine-by=handover"));
                        assert!(report.contains("handover=off"));
                    }
                }
            }
        }
    }
    // Plain-only runs tally every pair-update decision and the handover switch is type-checked.
    #[test]
    fn plain_tallies_and_bad_types() {
        let mut request = cases().remove(1);
        request["research_signatures"] = json!(false);
        let result = solve(&request).unwrap();
        let p = &result["research_signature"]["plain_pairs"];
        assert!(p["updates"].as_u64().unwrap() > 0);
        assert!(p["kept"].as_u64().unwrap() > 0);
        request["research_handover"] = json!("off");
        assert!(solve(&request).is_err());
    }
}
