// Research instrument for #731: where scalar Wiedemann conversion spends its time, and what
// batching projections or a block Krylov sequence would and would not remove. Nothing here is
// called by the library; `docs/research/block-krylov-conversion.md` holds the method and results.
use std::{
    env,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, SeedableRng};
use zeebra::{
    fields::{BabyBear, Zp18446744069414584321 as Goldilocks, Zp65537},
    grobner::fglm::{
        fglm_to_lex_with_options, ConversionStrategy, FglmOptions, MultiplicationOperator,
        QuotientAlgebra,
    },
    util::{isa_floor, peak_resident_bytes, sha256_hex},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// Column-major copy of a multiplication operator that keeps the native unit-column shortcut.
///
/// `MultiplicationOperator::apply_transpose` is crate-private, so the sequence arms run this
/// mirror; the `native` arm and the production `scalar_sequence` stage calibrate it.
pub struct Mirror<F> {
    columns: Vec<Column<F>>,
}

enum Column<F> {
    Unit(usize),
    Sparse(Box<[(usize, F)]>),
}

impl<F: FiniteField> Mirror<F> {
    pub fn new(op: &MultiplicationOperator<F>) -> Self {
        let columns = (0..op.dimension())
            .map(|j| match op.column_entries(j).as_slice() {
                [(k, c)] if c.is_one() => Column::Unit(*k),
                entries => Column::Sparse(entries.into()),
            })
            .collect();
        Self { columns }
    }

    pub fn dimension(&self) -> usize {
        self.columns.len()
    }

    /// `y = A^T x` on `w` interleaved vectors (`x[k * w + b]`), overwriting `y`.
    pub fn transpose_block(&self, x: &[F], w: usize, y: &mut [F]) {
        debug_assert_eq!(x.len(), self.columns.len() * w);
        debug_assert_eq!(y.len(), x.len());
        // Width one gets the production-shaped loop, so batching is not credited with indexing.
        if w == 1 {
            for (column, out) in self.columns.iter().zip(y.iter_mut()) {
                *out = match column {
                    Column::Unit(k) => x[*k],
                    Column::Sparse(entries) => entries
                        .iter()
                        .map(|(k, c)| x[*k] * *c)
                        .fold(F::zero(), |p, q| p + q),
                };
            }
            return;
        }
        for (column, out) in self.columns.iter().zip(y.chunks_exact_mut(w)) {
            match column {
                Column::Unit(k) => out.copy_from_slice(&x[k * w..(k + 1) * w]),
                Column::Sparse(entries) => {
                    out.fill(F::zero());
                    for (k, c) in entries.iter() {
                        for (slot, value) in out.iter_mut().zip(&x[k * w..(k + 1) * w]) {
                            *slot += *c * *value;
                        }
                    }
                }
            }
        }
    }
}

/// Every projection's sequence `s[b][i][k] = <(A^T)^k r_b, u_i>` for `k < len`, `u_i` sparse.
pub type Sequences<F> = Vec<Vec<Vec<F>>>;

/// One width-1 sweep per projection, two reused buffers: the production recurrence.
pub fn serial<F: FiniteField>(
    a: &Mirror<F>,
    projections: &[Vec<F>],
    left: &[Vec<(usize, F)>],
    len: usize,
) -> Sequences<F> {
    projections
        .iter()
        .map(|r| batched(a, std::slice::from_ref(r), left, len).remove(0))
        .collect()
}

/// One sweep of width `projections.len()`: each operator entry is loaded once per step.
pub fn batched<F: FiniteField>(
    a: &Mirror<F>,
    projections: &[Vec<F>],
    left: &[Vec<(usize, F)>],
    len: usize,
) -> Sequences<F> {
    let (d, w) = (a.dimension(), projections.len());
    let mut x = vec![F::zero(); d * w];
    for (b, r) in projections.iter().enumerate() {
        for (k, value) in r.iter().enumerate() {
            x[k * w + b] = *value;
        }
    }
    let mut y = x.clone();
    let mut out = vec![vec![Vec::with_capacity(len); left.len()]; w];
    for step in 0..len {
        for (i, u) in left.iter().enumerate() {
            for (b, sequence) in out.iter_mut().enumerate() {
                let dot = u
                    .iter()
                    .map(|(k, c)| *c * x[k * w + b])
                    .fold(F::zero(), |p, q| p + q);
                sequence[i].push(dot);
            }
        }
        if step + 1 < len {
            a.transpose_block(&x, w, &mut y);
            std::mem::swap(&mut x, &mut y);
        }
    }
    out
}

/// Each projection's width-1 sweep on its own thread: concurrent, not less work, and no barrier.
pub fn threaded<F: FiniteField + Send + Sync>(
    a: &Mirror<F>,
    projections: &[Vec<F>],
    left: &[Vec<(usize, F)>],
    len: usize,
) -> Sequences<F> {
    std::thread::scope(|scope| {
        let handles: Vec<_> = projections
            .iter()
            .map(|r| scope.spawn(move || serial(a, std::slice::from_ref(r), left, len).remove(0)))
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("sequence worker"))
            .collect()
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    /// `x_i^5 - x_{i+1}`, `x_{N-1}^5 - x_0 - 1`: the certified-wiedemann.md family, shape position.
    Cyclic,
    /// `x_i^5 - (i + 2)`: radical, but `x_{N-1}` has a degree-5 minimal polynomial (non-shape).
    Powers,
    /// `x_i^5 - x_{i+1}`, `x_{N-1}^5 - x_0^2`: a double point at the origin, not shape in `x_{N-1}`.
    Nonradical,
    /// Cyclic with every monomial of degree at most two added to the last tail: denser operator.
    Dense,
}

fn source<const N: usize, F: FiniteField>(family: Family) -> Vec<MultivariatePolynomial<N, F>> {
    let names: [String; N] = std::array::from_fn(|i| format!("x{i}"));
    let names: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let mut quadratic = Vec::new();
    for i in 0..N {
        quadratic.push(format!("x{i}"));
        for j in i..N {
            quadratic.push(format!("x{i}*x{j}"));
        }
    }
    let dense_tail: String = quadratic
        .iter()
        .enumerate()
        .map(|(k, m)| format!("-{}*{m}", (7 * k + 3) % 97 + 1))
        .collect();
    (0..N)
        .map(|i| {
            let text = match (family, i + 1 < N) {
                (Family::Powers, _) => format!("x{i}^5-{}", i + 2),
                (_, true) => format!("x{i}^5-x{}", i + 1),
                (Family::Cyclic, false) => format!("x{i}^5-x0-1"),
                (Family::Nonradical, false) => format!("x{i}^5-x0^2"),
                (Family::Dense, false) => format!("x{i}^5-x0-1{dense_tail}"),
            };
            MultivariatePolynomial::parse(&text, names).expect("family polynomial")
        })
        .collect()
}

#[derive(Debug)]
struct Args {
    mode: String,
    family: Family,
    field: String,
    variables: usize,
    route: String,
    repeats: usize,
    widths: Vec<usize>,
}

impl Args {
    fn parse() -> Self {
        let mut args = Self {
            mode: "stages".into(),
            family: Family::Cyclic,
            field: "zp65537".into(),
            variables: 5,
            route: "wiedemann".into(),
            repeats: 5,
            widths: vec![2, 4, 8],
        };
        let mut input = env::args().skip(1);
        while let Some(flag) = input.next() {
            if flag == "--help" {
                println!("block_krylov_study [--mode stages|sequence] [--family cyclic|powers|nonradical|dense] [--field zp65537|babybear|goldilocks] [--variables 3..7] [--route wiedemann|classical|adaptive] [--repeats N] [--widths 2,4,8]");
                std::process::exit(0);
            }
            let value = input.next().expect("every flag takes a value");
            match flag.as_str() {
                "--mode" => args.mode = value,
                "--family" => {
                    args.family = match value.as_str() {
                        "cyclic" => Family::Cyclic,
                        "powers" => Family::Powers,
                        "nonradical" => Family::Nonradical,
                        "dense" => Family::Dense,
                        _ => panic!("unknown family {value}"),
                    }
                }
                "--field" => args.field = value,
                "--variables" => args.variables = value.parse().expect("variable count"),
                "--route" => args.route = value,
                "--repeats" => args.repeats = value.parse().expect("repeat count"),
                "--widths" => {
                    args.widths = value
                        .split(',')
                        .map(|w| w.parse().expect("width"))
                        .collect()
                }
                _ => panic!("unknown argument {flag}"),
            }
        }
        args
    }
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.
}

fn load() -> f64 {
    std::fs::read_to_string("/proc/loadavg")
        .ok()
        .and_then(|s| s.split_whitespace().next().and_then(|t| t.parse().ok()))
        .unwrap_or(f64::NAN)
}

fn options(strategy: ConversionStrategy) -> FglmOptions {
    FglmOptions {
        conversion_strategy: strategy,
        max_quotient_dimension: 100_000,
        max_span_entries: usize::MAX,
        max_span_bytes: usize::MAX,
        max_operator_entries: usize::MAX,
        max_operator_bytes: usize::MAX,
        measure_stages: true,
        ..FglmOptions::recommended()
    }
}

/// One conversion per process so peak RSS is attributable to one route.
fn stages<const N: usize, F: FiniteField>(args: &Args, basis: &[MultivariatePolynomial<N, F>]) {
    let strategy = match args.route.as_str() {
        "classical" => ConversionStrategy::Classical,
        "adaptive" => ConversionStrategy::Adaptive,
        _ => ConversionStrategy::Wiedemann,
    };
    let order = MonomialOrder::GradedReverseLexicographic;
    let algebra = QuotientAlgebra::new(basis, order, &options(strategy)).expect("operators");
    let op = algebra.operator(N - 1);
    println!(
        "operator D={} entries={} standard-columns={} dense-columns={} stored-bytes={}",
        op.dimension(),
        op.stored_entries(),
        op.standard_columns(),
        op.dense_columns(),
        op.stored_bytes()
    );
    drop(algebra);
    println!("repeat route selected attempts fallback D wall-ms operator-ms sequence-ms reconstruction-ms certificate-ms dependence-ms other-ms load basis-sha256");
    let mut reference = None;
    for repeat in 0..args.repeats {
        let start = Instant::now();
        let (lex, stats) = fglm_to_lex_with_options(basis, order, &options(strategy))
            .expect("conversion within budgets");
        let wall = start.elapsed();
        let digest = sha256_hex(
            lex.iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
                .as_bytes(),
        );
        match &reference {
            Some(previous) => assert_eq!(previous, &digest, "repeats disagree"),
            None => reference = Some(digest.clone()),
        }
        let t = &stats.timings;
        println!(
            "{} {:?} {:?} {} {:?} {} {:.3} {:.3} {:.3} {:.3} {:.3} {:.3} {:.3} {:.2} {}",
            repeat + 1,
            strategy,
            stats.conversion_route,
            stats.wiedemann_attempts,
            stats.wiedemann_fallback,
            stats.quotient_dimension,
            ms(wall),
            ms(t.operator_construction()),
            ms(t.scalar_sequence),
            ms(t.scalar_reconstruction),
            ms(t.scalar_certificate),
            ms(t.dependence),
            ms(wall.saturating_sub(t.operator_construction() + t.dependence)),
            load(),
            digest
        );
    }
}

/// Block Krylov sequence length for an `m x n` block with `m = n = w`.
fn block_length(d: usize, w: usize) -> usize {
    2 * d.div_ceil(w)
}

fn sequence<const N: usize, F: FiniteField + Send + Sync>(
    args: &Args,
    basis: &[MultivariatePolynomial<N, F>],
) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let algebra = QuotientAlgebra::new(basis, order, &options(ConversionStrategy::Wiedemann))
        .expect("operators");
    let op = algebra.operator(N - 1);
    let a = Mirror::new(op);
    let d = a.dimension();
    let sparse = |v: Vec<F>| -> Vec<(usize, F)> {
        v.into_iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .collect()
    };
    // The production moment queries: the class of 1, then of each non-last variable.
    let classes: Vec<Vec<(usize, F)>> = std::iter::once(algebra.one())
        .chain((0..N - 1).map(|i| algebra.multiply_by_variable(i, &algebra.one())))
        .map(sparse)
        .collect();
    let mut rng = StdRng::seed_from_u64(0x731);
    let widest = *args.widths.iter().max().unwrap_or(&1);
    let projections: Vec<Vec<F>> = (0..widest)
        .map(|_| (0..d).map(|_| F::random(&mut rng)).collect())
        .collect();
    // A sparse left block: the production classes, then coordinate unit vectors.
    let block_left = |w: usize| -> Vec<Vec<(usize, F)>> {
        classes
            .iter()
            .cloned()
            .chain((1..).map(|k| vec![(k % d, F::one())]))
            .take(w)
            .collect()
    };
    println!(
        "D={d} steps-scalar={} left-classes-nnz={}",
        2 * d,
        classes.iter().map(Vec::len).sum::<usize>()
    );
    type Run<'a, F> = Box<dyn Fn() -> Sequences<F> + 'a>;
    let mut arms: Vec<(String, Run<F>)> = Vec::new();
    let p1 = &projections[..1];
    arms.push((
        "native-apply 1x2D".into(),
        Box::new(|| {
            let mut v = projections[0].clone();
            for _ in 0..2 * d {
                v = op.apply(&v);
            }
            vec![vec![v]]
        }),
    ));
    arms.push((
        "scalar 1x2D".into(),
        Box::new(|| serial(&a, p1, &classes, 2 * d)),
    ));
    for &w in &args.widths {
        let p = &projections[..w];
        let (a, classes) = (&a, &classes);
        arms.push((
            format!("indep-serial {w}x2D"),
            Box::new(move || serial(a, p, classes, 2 * d)),
        ));
        arms.push((
            format!("indep-batched {w}x2D"),
            Box::new(move || batched(a, p, classes, 2 * d)),
        ));
        arms.push((
            format!("indep-threads {w}x2D"),
            Box::new(move || threaded(a, p, classes, 2 * d)),
        ));
        let left = block_left(w);
        let len = block_length(d, w);
        arms.push((
            format!("block-batched {w}x{len}"),
            Box::new(move || batched(a, p, &left, len)),
        ));
        let left = block_left(w);
        arms.push((
            format!("block-threads {w}x{len}"),
            Box::new(move || threaded(a, p, &left, len)),
        ));
    }
    let mut samples = vec![Vec::new(); arms.len()];
    for repeat in 0..args.repeats {
        // Rotate the arm order each repetition so drift does not favour one position.
        for offset in 0..arms.len() {
            let index = (offset + repeat) % arms.len();
            let start = Instant::now();
            let out = (arms[index].1)();
            samples[index].push(start.elapsed());
            std::hint::black_box(out);
        }
        println!("repeat {} done load={:.2}", repeat + 1, load());
    }
    // Ratios are paired per repetition against that repetition's scalar arm.
    println!("| arm | median ms | min ms | max ms | median ratio to scalar |");
    println!("|---|---:|---:|---:|---:|");
    for (index, (name, _)) in arms.iter().enumerate() {
        let mut values: Vec<f64> = samples[index].iter().map(|t| ms(*t)).collect();
        let mut ratios: Vec<f64> = values
            .iter()
            .zip(&samples[1])
            .map(|(v, s)| v / ms(*s))
            .collect();
        values.sort_by(f64::total_cmp);
        ratios.sort_by(f64::total_cmp);
        println!(
            "| {name} | {:.3} | {:.3} | {:.3} | {:.3} |",
            values[values.len() / 2],
            values[0],
            values[values.len() - 1],
            ratios[ratios.len() / 2]
        );
    }
}

fn run<const N: usize, F: FiniteField + Send + Sync>(args: &Args) {
    let basis = source::<N, F>(args.family);
    let text = basis
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    println!(
        "family={:?} field={} variables={N} source-sha256={} isa={} machine={} affinity={} load={:.2}",
        args.family,
        args.field,
        sha256_hex(text.as_bytes()),
        isa_floor(),
        env::var("ZEEBRA_MACHINE").unwrap_or_else(|_| "unspecified".into()),
        env::var("ZEEBRA_AFFINITY").unwrap_or_else(|_| "unspecified".into()),
        load()
    );
    match args.mode.as_str() {
        "stages" => stages(args, &basis),
        "sequence" => sequence(args, &basis),
        mode => panic!("unknown mode {mode}"),
    }
    println!("process-peak-rss-bytes={:?}", peak_resident_bytes());
}

fn main() {
    let args = Args::parse();
    macro_rules! dispatch {
        ($field:ty) => {
            match args.variables {
                3 => run::<3, $field>(&args),
                4 => run::<4, $field>(&args),
                5 => run::<5, $field>(&args),
                6 => run::<6, $field>(&args),
                7 => run::<7, $field>(&args),
                n => panic!("supported variable counts are 3 through 7, not {n}"),
            }
        };
    }
    match args.field.as_str() {
        "zp65537" => dispatch!(Zp65537),
        "babybear" => dispatch!(BabyBear),
        "goldilocks" => dispatch!(Goldilocks),
        field => panic!("unknown field {field}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::{One, Zero};

    fn algebra<const N: usize>(family: Family) -> QuotientAlgebra<N, Zp65537> {
        let order = MonomialOrder::GradedReverseLexicographic;
        QuotientAlgebra::new(
            &source::<N, Zp65537>(family),
            order,
            &options(ConversionStrategy::Classical),
        )
        .unwrap()
    }

    fn random(d: usize, count: usize, seed: u64) -> Vec<Vec<Zp65537>> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..count)
            .map(|_| (0..d).map(|_| Zp65537::random(&mut rng)).collect())
            .collect()
    }

    fn dense_dot(u: &[(usize, Zp65537)], v: &[Zp65537]) -> Zp65537 {
        u.iter()
            .map(|(k, c)| *c * v[*k])
            .fold(Zp65537::zero(), |a, b| a + b)
    }

    // A width-w transpose block equals w independent transposes, checked against the forward apply.
    #[test]
    fn transpose_block_matches_forward_apply_adjoint() {
        let algebra = algebra::<3>(Family::Dense);
        let op = algebra.operator(2);
        let a = Mirror::new(op);
        let d = a.dimension();
        let xs = random(d, 3, 1);
        let mut block = vec![Zp65537::zero(); 3 * d];
        for (b, x) in xs.iter().enumerate() {
            for k in 0..d {
                block[k * 3 + b] = x[k];
            }
        }
        let mut out = vec![Zp65537::zero(); 3 * d];
        a.transpose_block(&block, 3, &mut out);
        // <A^T x, e_j> = <x, A e_j>, so column j of A dotted with x is coordinate j of A^T x.
        for (b, x) in xs.iter().enumerate() {
            for j in 0..d {
                assert_eq!(out[j * 3 + b], dense_dot(&op.column_entries(j), x));
            }
        }
    }

    // Serial, batched and threaded sequences are identical to the forward-apply oracle <r, A^k u>.
    #[test]
    fn every_arm_reproduces_the_forward_sequence() {
        for family in [Family::Cyclic, Family::Nonradical, Family::Dense] {
            let algebra = algebra::<3>(family);
            let op = algebra.operator(2);
            let a = Mirror::new(op);
            let d = a.dimension();
            let projections = random(d, 4, 2);
            let left: Vec<Vec<(usize, Zp65537)>> = vec![
                vec![(0, Zp65537::one())],
                vec![(d - 1, Zp65537::new(5)), (1, Zp65537::new(3))],
            ];
            let len = 2 * d;
            let reference = serial(&a, &projections, &left, len);
            for (b, r) in projections.iter().enumerate() {
                for (i, u) in left.iter().enumerate() {
                    let mut dense = vec![Zp65537::zero(); d];
                    for (k, c) in u {
                        dense[*k] = *c;
                    }
                    for k in 0..len {
                        let value = r
                            .iter()
                            .zip(&dense)
                            .map(|(x, y)| *x * *y)
                            .fold(Zp65537::zero(), |p, q| p + q);
                        assert_eq!(reference[b][i][k], value, "b={b} i={i} k={k}");
                        dense = op.apply(&dense);
                    }
                }
            }
            for width in [1, 2, 4] {
                let p = &projections[..width];
                assert_eq!(batched(&a, p, &left, len), reference[..width]);
                assert_eq!(threaded(&a, p, &left, len), reference[..width]);
            }
        }
    }

    // A zero projection yields all-zero sequences and a zero-length request yields empty ones.
    #[test]
    fn degenerate_inputs_are_exact() {
        let algebra = algebra::<3>(Family::Cyclic);
        let a = Mirror::new(algebra.operator(2));
        let d = a.dimension();
        let left = vec![vec![(0, Zp65537::one())]];
        let zero = vec![vec![Zp65537::zero(); d]; 2];
        assert_eq!(
            batched(&a, &zero, &left, 5),
            vec![vec![vec![Zp65537::zero(); 5]]; 2]
        );
        assert_eq!(
            batched(&a, &zero, &left, 0),
            vec![vec![Vec::<Zp65537>::new()]; 2]
        );
    }

    // Block sequence length is 2 ceil(D/w), so width one reproduces the scalar 2D.
    #[test]
    fn block_length_reduces_to_scalar() {
        assert_eq!(block_length(3125, 1), 6250);
        assert_eq!(block_length(3125, 8), 782);
    }
}
