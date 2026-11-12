//! Frozen F4 matrix replays separate native kernel timing from diagnostic row-work counting.
use std::{
    collections::{HashMap, HashSet},
    time::{Duration, Instant},
};
use zeebra::{
    fields::{Bn254Fr, Mersenne31, Zp18446744073709551557, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        differential::polynomial_to_string,
        external::{corpus, Instance},
        f4::{
            matrix_corpus::{self, capture_matrix, BatchSelector, MatrixSpec},
            structured::{self, BlockPlan},
            RowKind,
        },
        f4_reported, F4Options,
    },
    linalg::{
        sparse::{back_substitute_pivots_within, SparseMatrix},
        Backend,
    },
    util::{peak_resident_bytes, Json, Sha256},
    FiniteField, KnownOrder, MultivariatePolynomial,
};

#[derive(Clone, Copy, Debug, Default)]
struct Work {
    steps: usize,
    own_terms: usize,
    pivot_terms: usize,
    overlap_terms: usize,
    prefix_terms: usize,
    suffix_terms: usize,
    output_terms: usize,
    output_window_terms: usize,
}
impl Work {
    fn json(&self) -> Json {
        Json::object([
            ("steps", Json::size(self.steps)),
            ("own_terms", Json::size(self.own_terms)),
            ("pivot_terms", Json::size(self.pivot_terms)),
            ("overlap_terms", Json::size(self.overlap_terms)),
            ("prefix_terms", Json::size(self.prefix_terms)),
            ("suffix_terms", Json::size(self.suffix_terms)),
            ("output_terms", Json::size(self.output_terms)),
            ("output_window_terms", Json::size(self.output_window_terms)),
        ])
    }
}

fn work_replay<F: FiniteField>(
    matrix: &SparseMatrix<F>,
    scaffold: &HashSet<usize>,
    max_entries: usize,
) -> (SparseMatrix<F>, [Work; 2]) {
    let mut rows = matrix.rows().to_vec();
    let mut pivots: Vec<_> = rows
        .iter()
        .enumerate()
        .filter_map(|(i, r)| r.leading_column().map(|c| (c, i)))
        .collect();
    pivots.sort_unstable();
    let slots: HashMap<_, _> = pivots
        .iter()
        .enumerate()
        .map(|(s, (c, _))| (*c, s))
        .collect();
    let mut column_rows = vec![Vec::new(); pivots.len()];
    for (i, row) in rows.iter().enumerate() {
        for (column, _) in row.entries() {
            if let Some(&slot) = slots.get(column) {
                column_rows[slot].push(i);
            }
        }
    }
    let mut scratch = Vec::new();
    let mut resident = matrix.nonzeros();
    let mut counts = [Work::default(); 2];
    for (slot, &(column, pivot)) in pivots.iter().enumerate().rev() {
        for &target in &column_rows[slot] {
            if target == pivot {
                continue;
            }
            let factor = rows[target].coefficient(column);
            assert!(!factor.is_zero());
            let mut row = std::mem::take(&mut rows[target]);
            let role = usize::from(!scaffold.contains(&row.leading_column().unwrap()));
            let other = &rows[pivot];
            let lo = row.entries().partition_point(|(c, _)| *c < column);
            let hi = row
                .entries()
                .partition_point(|(c, _)| *c <= other.trailing_column().unwrap());
            let old_len = row.nonzeros();
            let prefix = lo;
            let suffix = old_len - hi;
            let work = &mut counts[role];
            work.steps += 1;
            work.own_terms += old_len;
            work.pivot_terms += other.nonzeros();
            work.overlap_terms += hi - lo;
            work.prefix_terms += prefix;
            work.suffix_terms += suffix;
            resident -= old_len;
            row.subtract_scaled(other, &factor, &mut scratch);
            resident += row.nonzeros();
            assert!(resident <= max_entries, "diagnostic entry cap");
            work.output_terms += row.nonzeros();
            work.output_window_terms += row.nonzeros() - prefix - suffix;
            rows[target] = row;
        }
    }
    let mut result = SparseMatrix::new(matrix.num_columns(), rows);
    result.sort_rows_by_leading_column();
    (result, counts)
}

fn matrix_hash<F: FiniteField>(matrix: &SparseMatrix<F>) -> String {
    let mut hash = Sha256::new();
    hash.update(format!("{}:{};", matrix.num_rows(), matrix.num_columns()).as_bytes());
    for row in matrix.rows() {
        hash.update(format!("r{}:", row.nonzeros()).as_bytes());
        for (column, value) in row.entries() {
            let text = value.to_string();
            hash.update(format!("{column}:{}:{text};", text.len()).as_bytes());
        }
    }
    hash.hex()
}

fn matrix<const N: usize, F: FiniteField>(
    spec: &MatrixSpec,
    system: &[MultivariatePolynomial<N, F>],
    backend: Backend,
    diagnose: bool,
) -> Json {
    let options = F4Options {
        max_wall_time: Some(Duration::from_secs(60)),
        ..spec.options.options()
    };
    let captured = capture_matrix(
        spec.label,
        system,
        spec.order,
        &options,
        BatchSelector::Prefix(spec.fingerprint.batch_index),
    )
    .expect("bounded exact capture");
    assert_eq!(
        captured.fingerprint, spec.fingerprint,
        "captured input drift"
    );
    let mut matrix = captured.matrix.clone();
    let scaffold: HashSet<_> = matrix
        .row_origins()
        .iter()
        .enumerate()
        .filter(|(_, r)| r.kind == RowKind::Reducer)
        .map(|(i, _)| matrix.matrix().row(i).leading_column().unwrap())
        .collect();
    let allowance = options.live_entry_allowance::<F>();
    let started = Instant::now();
    let mut outcome = structured::eliminate(
        BlockPlan::ReducersFirstBlock,
        backend,
        &mut matrix,
        allowance,
    )
    .expect("forward elimination cap");
    let forward = started.elapsed();
    let mut diagnostic = if diagnose {
        Some(matrix.matrix().clone())
    } else {
        None
    };
    let started = Instant::now();
    let rows =
        back_substitute_pivots_within(matrix.matrix_mut(), allowance, &mut outcome.statistics)
            .expect("back-substitution cap");
    let backward = started.elapsed();
    let mut fields = vec![
        (
            "mode",
            Json::string(if diagnose { "work" } else { "matrix" }),
        ),
        ("label", Json::string(spec.label)),
        ("field", Json::string(spec.field)),
        ("backend", Json::string(format!("{backend:?}"))),
        (
            "fingerprint",
            Json::string(format!("{:?}", captured.fingerprint)),
        ),
        ("options", Json::string(format!("{options:?}"))),
        ("forward_ns", Json::nanos(forward)),
        ("backward_ns", Json::nanos(backward)),
        ("elimination_ns", Json::nanos(forward + backward)),
        ("backward_rows", Json::size(rows)),
        (
            "statistics",
            Json::string(format!("{:?}", outcome.statistics)),
        ),
        ("rank", Json::size(matrix.matrix().nonzero_rows())),
        ("rref_hash", Json::string(matrix_hash(matrix.matrix()))),
        (
            "bytes_per_entry",
            Json::size(F4Options::bytes_per_entry::<F>()),
        ),
        (
            "dense_buffer_bytes",
            Json::size(if backend == Backend::Dense {
                matrix.num_rows() * matrix.num_columns() * std::mem::size_of::<F>()
            } else if backend == Backend::Adaptive {
                matrix.num_columns() * std::mem::size_of::<F>()
            } else {
                0
            }),
        ),
    ];
    if let Some(source) = diagnostic.take() {
        let (replayed, work) = work_replay(&source, &scaffold, allowance);
        assert_eq!(
            replayed,
            *matrix.matrix(),
            "diagnostic replay differs from production"
        );
        assert_eq!(work.iter().map(|w| w.steps).sum::<usize>(), rows);
        fields.extend([
            ("scaffold_pivot_targets", work[0].json()),
            ("new_pivot_targets", work[1].json()),
        ]);
    }
    fields.push((
        "process_peak_rss_bytes",
        peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
    ));
    Json::object(fields)
}

fn parsed<const N: usize, F: FiniteField + KnownOrder>(
    input: &Instance,
) -> Vec<MultivariatePolynomial<N, F>> {
    assert_eq!(
        F::characteristic_u128(),
        Some(input.field.characteristic as u128)
    );
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect()
}

fn solve<const N: usize, F: FiniteField + KnownOrder>(input: &Instance) -> Json {
    let system = parsed::<N, F>(input);
    let options = F4Options {
        measure_stages: true,
        max_wall_time: Some(Duration::from_secs(60)),
        ..F4Options::default()
    };
    let started = Instant::now();
    let (result, stats) = f4_reported(&system, input.order, &options);
    let elapsed = started.elapsed();
    let mut fields = vec![
        ("mode", Json::string("solve")),
        ("name", Json::string(&input.name)),
        ("digest", Json::string(input.digest())),
        ("modulus", Json::int(input.field.characteristic)),
        ("f4_call_ns", Json::nanos(elapsed)),
        ("options", Json::string(format!("{options:?}"))),
        ("statistics", Json::string(format!("{stats:#?}"))),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
    ];
    match result {
        Ok(basis) => {
            let names: Vec<_> = input.variables.iter().map(String::as_str).collect();
            let mut text: Vec<_> = basis
                .iter()
                .map(|p| polynomial_to_string(p, &names, input.order))
                .collect();
            text.sort();
            fields.extend([
                ("status", Json::string("complete")),
                (
                    "basis",
                    Json::Array(text.into_iter().map(Json::string).collect()),
                ),
            ]);
        }
        Err(e) => fields.extend([
            ("status", Json::string("stopped-by-limit")),
            ("error", Json::string(e.to_string())),
        ]),
    }
    Json::object(fields)
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let value = |key| {
        args.iter()
            .position(|s| s == key)
            .and_then(|i| args.get(i + 1))
            .map(String::as_str)
    };
    if value("--mode") == Some("solve") {
        let name = value("--row").expect("--row");
        let p = value("--modulus").unwrap_or("32003").parse().unwrap();
        let input =
            corpus::instance(name, p, zeebra::MonomialOrder::GradedReverseLexicographic).unwrap();
        let entry = corpus::ladder()
            .into_iter()
            .find(|e| e.name == name)
            .unwrap();
        assert_eq!(entry.digest_at(p), Some(input.digest().as_str()));
        let result = match (name, p) {
            ("cyclic-5", 32003) => solve::<5, Zp32003>(&input),
            ("katsura-4", 32003) => solve::<4, Zp32003>(&input),
            ("cyclic-5", 2147483647) => solve::<5, Zp2147483647>(&input),
            ("katsura-4", 2147483647) => solve::<4, Zp2147483647>(&input),
            _ => panic!("registered solve controls: cyclic-5/katsura-4 at 32003/2147483647"),
        };
        println!("{}", result.to_json());
        return;
    }
    let label = value("--matrix").expect("--matrix (frozen corpus label)");
    let spec = matrix_corpus::corpus()
        .into_iter()
        .find(|s| s.label == label)
        .expect("registered matrix");
    let backend = match value("--backend").unwrap_or("adaptive") {
        "sparse" => Backend::Sparse,
        "dense" => Backend::Dense,
        "adaptive" => Backend::Adaptive,
        _ => panic!("backend"),
    };
    let work = value("--mode") == Some("work");
    let result = match label {
        "katsura-7/grevlex/m31/default" => {
            matrix(&spec, &katsura::<7, Mersenne31>(), backend, work)
        }
        "cyclic-6/grevlex/m31/default" => matrix(&spec, &cyclic::<6, Mersenne31>(), backend, work),
        "katsura-6/lex/m31/baseline" => matrix(&spec, &katsura::<6, Mersenne31>(), backend, work),
        "katsura-7/grevlex/p64/default" => matrix(
            &spec,
            &katsura::<7, Zp18446744073709551557>(),
            backend,
            work,
        ),
        "cyclic-6/grevlex/p64/default" => {
            matrix(&spec, &cyclic::<6, Zp18446744073709551557>(), backend, work)
        }
        "katsura-6/lex/p64/baseline" => matrix(
            &spec,
            &katsura::<6, Zp18446744073709551557>(),
            backend,
            work,
        ),
        "katsura-6/grevlex/bn254/default" => matrix(&spec, &katsura::<6, Bn254Fr>(), backend, work),
        "cyclic-5/grevlex/bn254/baseline" => matrix(&spec, &cyclic::<5, Bn254Fr>(), backend, work),
        "mq-random-10/grevlex/p31x64/default" => {
            let input = corpus::instance(
                "mq-random-10",
                2147483647,
                zeebra::MonomialOrder::GradedReverseLexicographic,
            )
            .unwrap();
            matrix(&spec, &parsed::<10, Zp2147483647>(&input), backend, work)
        }
        _ => panic!("label has no experiment dispatch"),
    };
    println!("{}", result.to_json());
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::fields::Zp13;
    use zeebra::linalg::sparse::{reduced_row_echelon, SparseRow};

    // Diagnostic counts distinguish scaffold targets and skip untouched prefixes while reproducing production RREF.
    #[test]
    fn work_counts_match_the_production_reduction() {
        let input = SparseMatrix::new(
            3,
            vec![
                SparseRow::<Zp13>::new(&[(0, Zp13::new(1)), (1, Zp13::new(1))]),
                SparseRow::new(&[(1, Zp13::new(1)), (2, Zp13::new(1))]),
            ],
        );
        let mut expected = input.clone();
        reduced_row_echelon(&mut expected);
        let (actual, counts) = work_replay(&input, &HashSet::from([0]), 100);
        assert_eq!(counts[0].steps, 1);
        assert_eq!(counts[1].steps, 0);
        assert_eq!(counts[0].own_terms, 2);
        assert_eq!(counts[0].overlap_terms, 1);
        assert_eq!(counts[0].prefix_terms, 1);
        assert_eq!(actual, expected);
    }
}
