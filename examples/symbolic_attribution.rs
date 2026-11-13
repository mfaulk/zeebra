//! Replays frozen F4 batches so symbolic ablations cannot change the pair trajectory.
use std::collections::{HashMap, HashSet};
use zeebra::{
    fields::Zp32003,
    grobner::{
        external::corpus,
        f4::{
            macaulay::MacaulayMatrix,
            observer::trace_batches,
            structured::{self, BlockPlan, RowForm},
            symbolic::*,
        },
        pairs::CriticalPair,
        F4Options,
    },
    linalg::work,
    Monomial, MonomialOrder, MultivariatePolynomial,
};

type F = Zp32003;

#[derive(Clone, Copy)]
enum Choice {
    First,
    Newest,
    Sparse,
    InputOrder(usize),
}

fn eligible<const N: usize>(basis: &MonicBasis<N, F>, active: bool) -> Vec<usize> {
    (0..basis.len())
        .filter(|&i| {
            !active
                || !(0..basis.len()).any(|j| {
                    i != j
                        && basis
                            .element(i)
                            .leading_monomial
                            .checked_div(&basis.element(j).leading_monomial)
                            .is_some()
                        && (basis.element(i).leading_monomial != basis.element(j).leading_monomial
                            || j < i)
                })
        })
        .collect()
}

fn replay<const N: usize>(
    basis: &MonicBasis<N, F>,
    pairs: &[CriticalPair<N>],
    choice: Choice,
    active: bool,
    deduplicate: bool,
) -> Preprocessed<N> {
    let mut rows = Vec::new();
    let mut covered = MonomialSet::default();
    let mut seeds = HashSet::new();
    for (position, pair) in pairs.iter().enumerate() {
        covered.insert(pair.lcm);
        for basis_index in [pair.left, pair.right] {
            let multiplier = pair
                .lcm
                .checked_div(&basis.element(basis_index).leading_monomial)
                .unwrap();
            if !deduplicate || seeds.insert((basis_index, multiplier)) {
                rows.push(PreprocessedRow {
                    basis_index,
                    multiplier,
                    kind: RowKind::PairComponent { pair: position },
                });
            }
        }
    }
    let mut candidates = eligible(basis, active);
    if let Choice::InputOrder(input_count) = choice {
        let initial = candidates.partition_point(|&i| i < input_count);
        candidates[..initial].sort_by(|&i, &j| {
            basis.order().cmp(
                &basis.element(i).leading_monomial,
                &basis.element(j).leading_monomial,
            )
        });
    }
    let mut monomials = Vec::new();
    let mut handles = HashMap::new();
    let mut term_handles = Vec::new();
    let mut add_terms = |row: &PreprocessedRow<N>, monomials: &mut Vec<Monomial<N>>| {
        for (m, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
            let next = u32::try_from(monomials.len()).unwrap();
            let handle = *handles.entry(m).or_insert_with(|| {
                monomials.push(m);
                next
            });
            term_handles.push(handle);
        }
    };
    for row in &rows {
        add_terms(row, &mut monomials);
    }
    let mut cursor = 0;
    while cursor < monomials.len() {
        let m = monomials[cursor];
        cursor += 1;
        if covered.contains(&m) {
            continue;
        }
        let divisors = || {
            candidates
                .iter()
                .copied()
                .filter(|&i| m.checked_div(&basis.element(i).leading_monomial).is_some())
        };
        let selected = match choice {
            Choice::First | Choice::InputOrder(_) => divisors().next(),
            Choice::Newest => divisors().next_back(),
            Choice::Sparse => divisors().min_by_key(|&i| (basis.element(i).terms.len(), i)),
        };
        if let Some(basis_index) = selected {
            let multiplier = m
                .checked_div(&basis.element(basis_index).leading_monomial)
                .unwrap();
            let row = PreprocessedRow {
                basis_index,
                multiplier,
                kind: RowKind::Reducer,
            };
            covered.insert(m);
            add_terms(&row, &mut monomials);
            rows.push(row);
            assert!(rows.len() <= 200_000, "replay row budget exceeded");
        }
    }
    Preprocessed {
        rows,
        leading_monomials: covered,
        monomials,
        term_handles,
        counts: SymbolicCounts::default(),
    }
}

fn main() {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance("mq-random-10", 32003, order).unwrap();
    let names: [&str; 10] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<10, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let options = F4Options::default();
    let (basis, _, trace) = trace_batches(&system, order, &options).unwrap();
    println!(
        "# mq-random-10 GF(32003) digest {} reduced_basis {}",
        input.digest(),
        basis.len()
    );
    println!("round\tarm\tpairs\tbasis\texcluded\tseeds\trows\tcols\tnnz\tforward_apps\tforward_products");
    for (round, batch) in trace.batches().iter().enumerate() {
        let baseline = symbolic_preprocessing(&batch.basis, &batch.pairs);
        for (name, choice, active, dedup) in [
            ("baseline", Choice::First, false, false),
            ("dedup", Choice::First, false, true),
            ("active", Choice::First, true, false),
            ("active-dedup", Choice::First, true, true),
            ("newest", Choice::Newest, false, false),
            ("sparse", Choice::Sparse, false, false),
            (
                "input-order",
                Choice::InputOrder(system.len()),
                false,
                false,
            ),
            (
                "input-order-dedup",
                Choice::InputOrder(system.len()),
                false,
                true,
            ),
            (
                "input-order-active-dedup",
                Choice::InputOrder(system.len()),
                true,
                true,
            ),
        ] {
            let pre = replay(&batch.basis, &batch.pairs, choice, active, dedup);
            if name == "baseline" {
                assert_eq!(pre.rows, baseline.rows);
                assert_eq!(pre.monomials, baseline.monomials);
                assert_eq!(pre.term_handles, baseline.term_handles);
                assert_eq!(pre.leading_monomials, baseline.leading_monomials);
            }
            if name == "dedup" {
                assert_eq!(pre.monomials, baseline.monomials);
                assert_eq!(pre.leading_monomials, baseline.leading_monomials);
            }
            let seeds = pre
                .rows
                .iter()
                .filter(|r| matches!(r.kind, RowKind::PairComponent { .. }))
                .count();
            let mut matrix = MacaulayMatrix::build(&batch.basis, &pre, order);
            let (rows, cols, nnz) = (matrix.num_rows(), matrix.num_columns(), matrix.nonzeros());
            let (_, counts) = work::measure(|| {
                structured::eliminate_to(
                    BlockPlan::ReducersFirstBlock,
                    RowForm::Reduced,
                    options.elimination,
                    &mut matrix,
                    options.max_live_nonzeros,
                )
                .unwrap()
            });
            let forward = counts.outside_batch.forward;
            println!(
                "{}\t{name}\t{}\t{}\t{}\t{seeds}\t{rows}\t{cols}\t{nnz}\t{}\t{}",
                round + 1,
                batch.pairs.len(),
                batch.basis.len(),
                batch.basis.len() - eligible(&batch.basis, active).len(),
                forward.pivot_applications,
                forward.coefficient_products
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (MonicBasis<3, F>, Vec<CriticalPair<3>>) {
        let order = MonomialOrder::GradedReverseLexicographic;
        let system: Vec<_> = ["x^2 + y*z + 1", "x*y + z", "y^2 + x", "x + z"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y", "z"]).unwrap())
            .collect();
        let pairs = vec![
            CriticalPair::new(&system, 0, 1, order),
            CriticalPair::new(&system, 1, 2, order),
        ];
        (MonicBasis::new(&system, order), pairs)
    }

    // The independent replay reproduces production rows, column order and term handles exactly.
    #[test]
    fn baseline_matches_production() {
        let (basis, pairs) = fixture();
        let actual = replay(&basis, &pairs, Choice::First, false, false);
        let expected = symbolic_preprocessing(&basis, &pairs);
        assert_eq!(actual.rows, expected.rows);
        assert_eq!(actual.monomials, expected.monomials);
        assert_eq!(actual.leading_monomials, expected.leading_monomials);
        assert_eq!(actual.term_handles, expected.term_handles);
    }

    // Repeated pair multiples remove seed rows without changing the symbolic column set.
    #[test]
    fn duplicate_pair_has_no_new_columns() {
        let (basis, mut pairs) = fixture();
        pairs.push(pairs[0].clone());
        let full = replay(&basis, &pairs, Choice::First, false, false);
        let unique = replay(&basis, &pairs, Choice::First, false, true);
        assert_eq!(full.rows.len() - unique.rows.len(), 2);
        assert_eq!(full.monomials, unique.monomials);
        assert_eq!(full.leading_monomials, unique.leading_monomials);
    }

    // Sorting only input reducers by increasing lead changes the reducer selected for x squared.
    #[test]
    fn input_order_searches_smallest_initial_lead_first() {
        let (basis, pairs) = fixture();
        let rows = replay(&basis, &pairs, Choice::InputOrder(4), false, false);
        let square = MultivariatePolynomial::<3, F>::parse("x^2", ["x", "y", "z"])
            .unwrap()
            .leading_monomial(basis.order());
        let row = rows
            .rows
            .iter()
            .find(|row| {
                matches!(row.kind, RowKind::Reducer)
                    && basis.element(row.basis_index).leading_monomial * &row.multiplier == square
            })
            .unwrap();
        assert_eq!(row.basis_index, 3);
    }

    // Active filtering excludes divisible old leads and keeps the earlier of equal leads.
    #[test]
    fn active_filter_handles_divisibility_and_ties() {
        let (basis, _) = fixture();
        assert_eq!(eligible(&basis, true), vec![2, 3]);
        let polynomial = MultivariatePolynomial::parse("x + z", ["x", "y", "z"]).unwrap();
        let basis = MonicBasis::new(&[polynomial.clone(), polynomial], basis.order());
        assert_eq!(eligible(&basis, true), vec![0]);
        assert_eq!(eligible(&basis, false), vec![0, 1]);
    }
}
