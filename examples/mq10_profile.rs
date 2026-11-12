//! One digest-pinned MQ10 computation per process; optional stage clocks preserve default strategies.
use std::time::Instant;
use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        differential::polynomial_to_string, external::corpus, f4_with_options, F4Options,
        F4Statistics,
    },
    util::Json,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

fn statistics(s: &F4Statistics, measured: bool) -> Json {
    let time = |duration| {
        if measured {
            Json::nanos(duration)
        } else {
            Json::Null
        }
    };
    let t = s.stages;
    let c = t.construction_split;
    Json::object([
        ("total_ns", time(s.total)),
        ("symbolic_ns", time(t.symbolic)),
        ("construction_ns", time(t.construction)),
        ("elimination_ns", time(t.elimination)),
        ("extraction_ns", time(t.extraction)),
        ("interreduction_ns", time(t.interreduction)),
        ("other_ns", time(s.total.saturating_sub(t.sum()))),
        ("construction_collect_ns", time(c.collect)),
        ("construction_sort_ns", time(c.sort)),
        ("construction_map_ns", time(c.map)),
        ("construction_scatter_ns", time(c.scatter)),
        ("construction_scatter_rows_ns", time(c.scatter_rows)),
        ("construction_scatter_assemble_ns", time(c.scatter_assemble)),
        ("batches", Json::size(s.batches)),
        ("pairs_considered", Json::size(s.pairs_considered)),
        ("pairs_reduced", Json::size(s.pairs_reduced)),
        ("elements_added", Json::size(s.elements_added)),
        ("empty_batches", Json::size(s.empty_batches)),
        ("max_matrix_rows", Json::size(s.max_matrix_rows)),
        ("max_matrix_columns", Json::size(s.max_matrix_columns)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
        (
            "max_live_nonzeros_as_built",
            Json::size(s.max_live_nonzeros_as_built),
        ),
        ("row_operations", Json::size(s.row_operations)),
        ("reducer_rows_reused", Json::size(s.reducer_rows_reused)),
        ("divisor_queries", Json::size(s.divisor_queries)),
        ("divisor_scan_steps", Json::size(s.divisor_scan_steps)),
        ("peak_basis_elements", Json::size(s.peak_basis_elements)),
        ("peak_basis_terms", Json::size(s.peak_basis_terms)),
        (
            "degree_sequence",
            Json::Array(s.step_degrees.iter().map(|d| Json::int(*d)).collect()),
        ),
        ("full_statistics", Json::string(format!("{s:#?}"))),
    ])
}

fn run<F: FiniteField>(modulus: u64, measured: bool) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance("mq-random-10", modulus, order).expect("published MQ10");
    let entry = corpus::ladder()
        .into_iter()
        .find(|e| e.name == input.name)
        .unwrap();
    assert_eq!(entry.digest_at(modulus), Some(input.digest().as_str()));
    let names: [&str; 10] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<10, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options {
        measure_stages: measured,
        ..F4Options::default()
    };
    let started = Instant::now();
    let (basis, stats) =
        f4_with_options(&system, order, &options).expect("MQ10 fits the shipped budget");
    let elapsed = started.elapsed();
    let mut basis: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, &names, order))
        .collect();
    basis.sort();
    println!(
        "{}",
        Json::object([
            ("modulus", Json::int(modulus)),
            ("digest", Json::string(input.digest())),
            ("measured", Json::Bool(measured)),
            ("field_type", Json::string(std::any::type_name::<F>())),
            ("options", Json::string(format!("{options:?}"))),
            ("f4_call_ns", Json::nanos(elapsed)),
            (
                "peak_rss_bytes",
                zeebra::util::peak_resident_bytes()
                    .map(Json::int)
                    .unwrap_or(Json::Null)
            ),
            ("statistics", statistics(&stats, measured)),
            (
                "basis",
                Json::Array(basis.into_iter().map(Json::string).collect())
            ),
        ])
        .to_json()
    );
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let modulus: u64 = args
        .first()
        .expect("usage: mq10_profile MODULUS [--stages]")
        .parse()
        .unwrap();
    assert!(
        args.len() <= 2 && args.get(1).is_none_or(|s| s == "--stages"),
        "unexpected argument"
    );
    let measured = args.len() == 2;
    match modulus {
        32003 => run::<Zp32003>(modulus, measured),
        2147483647 => run::<Zp2147483647>(modulus, measured),
        _ => panic!("supported moduli: 32003, 2147483647"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // Refining timers are excluded from the partition, so stage shares never double count them.
    #[test]
    fn stage_partition_excludes_refinements() {
        let mut s = F4Statistics {
            total: Duration::from_millis(20),
            ..Default::default()
        };
        s.stages.symbolic = Duration::from_millis(3);
        s.stages.construction = Duration::from_millis(4);
        s.stages.construction_split.scatter = Duration::from_millis(4);
        s.stages.elimination = Duration::from_millis(8);
        s.stages.extraction = Duration::from_millis(1);
        s.stages.interreduction = Duration::from_millis(2);
        s.stages.interreduction_reduce = Duration::from_millis(2);
        let report = statistics(&s, true);
        assert_eq!(
            report.get("other_ns").and_then(Json::as_int),
            Some(2_000_000)
        );
        assert_eq!(
            report.get("total_ns").and_then(Json::as_int),
            Some(20_000_000)
        );
    }

    // Disabled clocks remain absent rather than publishing zero as a measured stage duration.
    #[test]
    fn disabled_clocks_are_absent() {
        assert_eq!(
            statistics(&F4Statistics::default(), false).get("total_ns"),
            Some(&Json::Null)
        );
    }
}
