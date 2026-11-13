#[cfg(test)]
mod randomization_contract_tests {
    use super::*;
    fn input() -> Value {
        json!({"variables":["x","y"],"modulus":32003,"order":"grevlex","workers":1,
            "mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
            "generators":["x^2+y^2-1","x*y-1"],"research_work":true})
    }
    // Every independent ablation and the plain residual guard preserve a known complete basis.
    #[test]
    fn independent_policies_preserve_the_complete_basis() {
        for modulus in [13, 32003, 2147483647] {
            let mut base = input();
            base["modulus"] = json!(modulus);
            let baseline = solve(&base).unwrap()["basis"].clone();
            for policy in ["native", "no-plain", "no-signature", "none"] {
                for signatures in [true, false] {
                    let mut request = base.clone();
                    request["research_policy"] = json!(policy);
                    request["research_signatures"] = json!(signatures);
                    request["research_validate"] = json!(!signatures);
                    let result = solve(&request).unwrap();
                    assert_eq!(result["basis"], baseline);
                    if !signatures {
                        let checks = result["research_audit"].as_array().unwrap();
                        assert!(!checks.is_empty());
                        assert!(checks.iter().all(|check| check["valid"] == true));
                    }
                }
            }
        }
    }
    // Invalid experiment types and validation of signature runs are refused explicitly.
    #[test]
    fn experiment_parameters_fail_closed() {
        for (key, value) in [
            ("research_policy", json!(1)),
            ("research_policy", json!("unknown")),
            ("research_seed", json!(-1)),
            ("research_signatures", json!("false")),
            ("research_validate", json!(1)),
            ("research_validate", json!(true)),
        ] {
            let mut request = input();
            request[key] = value;
            assert!(solve(&request).is_err(), "{key}");
        }
    }
    // Interrupted computation leaves no observer policy or residual-check state for a later solve.
    #[test]
    fn an_interrupted_run_does_not_poison_reuse() {
        let mut request = input();
        request["research_signatures"] = json!(false);
        request["research_validate"] = json!(true);
        request["wall_ns"] = json!(0);
        assert!(solve(&request).unwrap()["stopped"].is_string());
        request["wall_ns"] = json!(10000000000u64);
        let result = solve(&request).unwrap();
        assert!(result["stopped"].is_null());
        assert!(
            result["research_audit"]
                .as_array()
                .unwrap()
                .iter()
                .all(|r| r["valid"] == true)
        );
    }
}
