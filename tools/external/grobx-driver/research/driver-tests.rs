#[cfg(test)]
mod research_tests {
    use super::*;

    fn path(report: &str) -> Vec<String> {
        report
            .lines()
            .flat_map(|line| {
                line.split_whitespace()
                    .filter(|word| {
                        word.split_once('=').is_some_and(|(key, value)| {
                            [
                                "engine",
                                "engine-by",
                                "field",
                                "reduce",
                                "reduce-by",
                                "width",
                                "degree",
                                "pairs",
                                "rows",
                                "given",
                                "columns",
                                "entries",
                                "pivots",
                                "zero",
                                "zero-rows",
                                "reductions",
                                "subtracted",
                                "added",
                                "bands",
                                "left",
                                "rounds",
                                "reduced",
                                "elements",
                                "outcome",
                                "handover",
                                "verdict",
                            ]
                            .contains(&key)
                                && (key != "reduce" || value.parse::<f64>().is_err())
                        })
                    })
                    .map(str::to_owned)
            })
            .collect()
    }

    // Enabling passive counters preserves full bases and reported algebraic work at both MQ characteristics.
    #[test]
    fn observer_preserves_path_and_basis() {
        for p in [32003u64, 2147483647] {
            let mut input = json!({"variables":["x","y"],"modulus":p,"order":"grevlex",
                "workers":1,"mode":"raw","wall_ns":10000000000u64,"rss_bytes":1073741824u64,
                "generators":["x^2+y","x*y+1","y^2+x"]});
            let off = solve(&input).unwrap();
            input["research_work"] = json!(true);
            let on = solve(&input).unwrap();
            assert_eq!(on["basis"], off["basis"]);
            assert_eq!(
                path(on["report"].as_str().unwrap()),
                path(off["report"].as_str().unwrap())
            );
            assert!(off["work"].is_null());
            assert!(!on["work"]["matrices"].as_array().unwrap().is_empty());
        }
    }
}
