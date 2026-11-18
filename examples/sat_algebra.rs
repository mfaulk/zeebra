//! #220: what SAT costs and offers against Zeebra's algebra, on public Boolean systems only.
//!
//! `clauses` measures the ANF→CNF blow-up (Bard–Courtois–Jefferson: one Tseitin AND per monomial,
//! each XOR cut into chunks) on random planted MQ systems and on the Macaulay rows F4 builds from
//! them. `replay` takes every Macaulay matrix a real `GF(2)` F4 run builds, eliminates it with
//! `Dense`, `Sparse`, `Adaptive` and the bit-packed kernel, exports it as XOR constraints, and has
//! CryptoMiniSat solve them; rank and solution-space dimension are asserted equal before any time
//! is printed. `preprocess` runs kissat on a planted system with an affine layer, with and without
//! Zeebra's affine elimination first, and F4's `solve_one` on both. Every model is checked
//! against the original equations.
//!
//! The converter and the model lift here are measurement scaffolding, not a backend (#220 decided
//! against one; `docs/research/sat-and-algebra.md`). External tools come from
//! `tools/external/provision-sat.sh`:
//!
//! ```text
//! export ZEEBRA_EXT_PREFIX=/path/to/prefix   # holds bin/kissat and bin/cms-xor-driver
//! cargo run --release --example sat_algebra -- clauses
//! cargo run --release --example sat_algebra -- replay 3
//! cargo run --release --example sat_algebra -- preprocess 3
//! ```

use std::{
    collections::{BTreeSet, HashMap},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::Zp2,
    grobner::{
        f4::{
            macaulay::MacaulayMatrix,
            symbolic::{symbolic_preprocessing_with, ReducerCache},
        },
        field_equations::with_field_equations,
        solve_one, trace_batches,
        transform::eliminate_affine,
        F4Options,
    },
    linalg::{
        gf2::{reduced_row_echelon_packed, BitMatrix},
        row_echelon_with, Backend,
    },
    Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// A multilinear Boolean polynomial: each monomial a bit mask over the variables.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Anf {
    monomials: BTreeSet<u64>,
    constant: bool,
}

/// Reduces modulo the field equations (`x^2 = x`) and drops cancelled pairs.
fn anf<const N: usize>(polynomial: &MultivariatePolynomial<N, Zp2>) -> Anf {
    assert!(N <= 64, "monomials are 64-bit masks");
    let mut monomials = BTreeSet::new();
    let mut constant = false;
    for (monomial, coefficient) in polynomial.terms() {
        if coefficient.is_zero() {
            continue;
        }
        let mask = monomial
            .exponents()
            .iter()
            .enumerate()
            .filter(|(_, &e)| e > 0)
            .fold(0u64, |mask, (i, _)| mask | 1 << i);
        if mask == 0 {
            constant ^= true;
        } else if !monomials.insert(mask) {
            monomials.remove(&mask);
        }
    }
    Anf {
        monomials,
        constant,
    }
}

/// Whether the equation `p = 0` holds at the point whose bit `i` is `x_i`.
fn holds(equation: &Anf, point: u64) -> bool {
    let odd = equation
        .monomials
        .iter()
        .filter(|&&m| point & m == m)
        .count()
        % 2
        == 1;
    odd == equation.constant
}

struct Cnf {
    variables: usize,
    clauses: Vec<Vec<i64>>,
}

impl Cnf {
    fn fresh(&mut self) -> i64 {
        self.variables += 1;
        self.variables as i64
    }

    /// Every sign pattern of the wrong parity, forbidden: `2^(k-1)` clauses.
    fn xor(&mut self, variables: &[i64], rhs: bool) {
        let k = variables.len();
        if k == 0 {
            if rhs {
                self.clauses.push(Vec::new());
            }
            return;
        }
        for pattern in 0..1u64 << k {
            if (pattern.count_ones() % 2 == 1) == rhs {
                continue;
            }
            // Blocks the assignment `variable i = bit i of pattern`.
            let clause = variables
                .iter()
                .enumerate()
                .map(|(i, &v)| if pattern >> i & 1 == 1 { -v } else { v })
                .collect();
            self.clauses.push(clause);
        }
    }

    /// A long XOR as a chain of chunks of at most `cut` variables, linked by fresh variables.
    fn cut_xor(&mut self, variables: &[i64], rhs: bool, cut: usize) {
        assert!(cut >= 3, "a chunk must hold two inputs and a link");
        let mut rest = variables.to_vec();
        while rest.len() > cut {
            let link = self.fresh();
            let mut chunk: Vec<i64> = rest.drain(..cut - 1).collect();
            chunk.push(link);
            self.xor(&chunk, false);
            rest.insert(0, link);
        }
        self.xor(&rest, rhs);
    }

    fn dimacs(&self) -> String {
        let mut text = format!("p cnf {} {}\n", self.variables, self.clauses.len());
        for clause in &self.clauses {
            for literal in clause {
                text.push_str(&literal.to_string());
                text.push(' ');
            }
            text.push_str("0\n");
        }
        text
    }
}

/// `x_i` is DIMACS variable `i + 1`; each monomial of degree two or more gets one Tseitin AND,
/// shared across equations.
fn encode(system: &[Anf], variables: usize, cut: usize) -> Cnf {
    let mut cnf = Cnf {
        variables,
        clauses: Vec::new(),
    };
    let mut gates: HashMap<u64, i64> = HashMap::new();
    for equation in system {
        let mut xor = Vec::with_capacity(equation.monomials.len());
        for &mask in &equation.monomials {
            if mask.count_ones() == 1 {
                xor.push(mask.trailing_zeros() as i64 + 1);
                continue;
            }
            let gate = match gates.get(&mask) {
                Some(&gate) => gate,
                None => {
                    let gate = cnf.fresh();
                    let inputs: Vec<i64> = (0..64)
                        .filter(|i| mask >> i & 1 == 1)
                        .map(|i| i as i64 + 1)
                        .collect();
                    for &input in &inputs {
                        cnf.clauses.push(vec![-gate, input]);
                    }
                    let mut all = vec![gate];
                    all.extend(inputs.iter().map(|input| -input));
                    cnf.clauses.push(all);
                    gates.insert(mask, gate);
                    gate
                }
            };
            xor.push(gate);
        }
        cnf.cut_xor(&xor, equation.constant, cut);
    }
    cnf
}

/// Clauses and link variables [`Cnf::cut_xor`] spends on an XOR of `length`, without emitting it.
fn xor_cost(length: usize, cut: usize) -> (u64, u64) {
    let (mut length, mut clauses, mut links) = (length, 0u64, 0u64);
    while length > cut {
        clauses += 1 << (cut - 1);
        links += 1;
        length -= cut - 2;
    }
    if length > 0 {
        clauses += 1 << (length - 1);
    }
    (clauses, links)
}

fn random_bit(rng: &mut StdRng) -> Zp2 {
    if rng.gen_bool(0.5) {
        Zp2::one()
    } else {
        Zp2::zero()
    }
}

/// Random quadratics (each `x_i x_j`, `i <= j`, with probability `density`) and random affine
/// forms (each variable with probability one half), shifted to vanish at a planted point: #272's
/// construction, as `examples/gf2_f4_dispatch.rs` builds it, plus the affine layer.
fn planted<const N: usize>(
    seed: u64,
    quadratics: usize,
    affine: usize,
    density: f64,
) -> (Vec<MultivariatePolynomial<N, Zp2>>, [Zp2; N]) {
    let mut rng = StdRng::seed_from_u64(seed);
    let plant: [Zp2; N] = std::array::from_fn(|_| random_bit(&mut rng));
    let mut system = Vec::new();
    for index in 0..quadratics + affine {
        let mut terms = Vec::new();
        for i in 0..N {
            if index >= quadratics {
                if rng.gen_bool(0.5) {
                    terms.push((Monomial::univariate(i, 1), Zp2::one()));
                }
                continue;
            }
            for j in i..N {
                if rng.gen_bool(density) {
                    let mut exponents = [0u32; N];
                    exponents[i] += 1;
                    exponents[j] += 1;
                    terms.push((Monomial::new(&exponents), Zp2::one()));
                }
            }
        }
        let mut polynomial = MultivariatePolynomial::new(&terms);
        let value = polynomial.eval(&plant);
        polynomial += MultivariatePolynomial::new(&[(Monomial::one(), Zp2::zero() - value)]);
        system.push(polynomial);
    }
    (system, plant)
}

fn ext_bin(name: &str, override_var: &str) -> Option<PathBuf> {
    if let Ok(path) = env::var(override_var) {
        return Some(PathBuf::from(path));
    }
    let prefix = env::var("ZEEBRA_EXT_PREFIX").ok()?;
    let path = Path::new(&prefix).join("bin").join(name);
    path.exists().then_some(path)
}

fn scratch() -> PathBuf {
    let dir = env::temp_dir().join(format!("zeebra-sat-algebra-{}", std::process::id()));
    fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

fn micros(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e6
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn uncut_label(length: usize) -> String {
    if length == 0 {
        "0".into()
    } else {
        format!("2^{}", length - 1)
    }
}

// --- clauses ---------------------------------------------------------------------------------

fn clause_report(label: &str, system: &[Anf], variables: usize) {
    let longest = system.iter().map(|e| e.monomials.len()).max().unwrap_or(0);
    let terms: usize = system.iter().map(|e| e.monomials.len()).sum();
    print!(
        "| {label} | {} | {terms} | {longest} | {} |",
        system.len(),
        uncut_label(longest)
    );
    for cut in [3, 4, 5, 6] {
        let cnf = encode(system, variables, cut);
        print!(" {} / {} |", cnf.clauses.len(), cnf.variables);
    }
    println!();
}

fn macaulay_matrices<const N: usize>(
    system: &[MultivariatePolynomial<N, Zp2>],
) -> Vec<MacaulayMatrix<N, Zp2>> {
    let options = F4Options::default();
    let (_, _, trace) = trace_batches(system, ORDER, &options).expect("within limits");
    trace
        .batches()
        .iter()
        .filter_map(|batch| {
            let preprocessed = symbolic_preprocessing_with(
                &batch.basis,
                &batch.pairs,
                options.max_matrix_rows,
                options.reducer_selection,
                &mut ReducerCache::disabled(),
            )
            .ok()?;
            Some(MacaulayMatrix::build(&batch.basis, &preprocessed, ORDER))
        })
        .collect()
}

/// Each matrix row as an XOR over its columns, the constant column read as the right-hand side.
fn matrix_clause_report<const N: usize>(label: &str, matrices: &[MacaulayMatrix<N, Zp2>]) {
    let (mut longest, mut nonzeros, mut rows, mut cut4) = (0, 0usize, 0usize, 0u64);
    for macaulay in matrices {
        let constant = macaulay.columns().iter().position(Monomial::is_one);
        for row in macaulay.matrix().rows() {
            let length = row
                .entries()
                .iter()
                .filter(|(c, _)| Some(*c) != constant)
                .count();
            longest = longest.max(length);
            nonzeros += row.nonzeros();
            rows += 1;
            cut4 += xor_cost(length, 4).0;
        }
    }
    println!(
        "| {label} | {} | {rows} | {nonzeros} | {longest} | {} | {cut4} | {:.1} |",
        matrices.len(),
        uncut_label(longest),
        cut4 as f64 / nonzeros as f64
    );
}

fn clauses() {
    println!("## Q1: polynomial systems\n");
    println!("Clauses / variables after Tseitin ANDs and cutting each XOR at the given length.\n");
    println!("| instance | equations | ANF terms | longest XOR | uncut clauses for it | cut 3 | cut 4 | cut 5 | cut 6 |");
    println!("|---|---|---|---|---|---|---|---|---|");
    let (system, _) = planted::<20>(220, 20, 0, 0.5);
    clause_report(
        "MQ n=20 m=20",
        &system.iter().map(anf).collect::<Vec<_>>(),
        20,
    );
    let (system, _) = planted::<24>(1, 18, 6, 0.5);
    clause_report(
        "n=24: 18 quadratics + 6 affine",
        &system.iter().map(anf).collect::<Vec<_>>(),
        24,
    );
    let (remaining, record) = eliminate_affine(&system);
    let projected = record
        .project::<18>(&remaining)
        .expect("six affine forms, six variables gone");
    clause_report(
        "same, affine-eliminated (n=18)",
        &projected.iter().map(anf).collect::<Vec<_>>(),
        18,
    );

    println!("\n## Q1: Macaulay rows of a real GF(2) F4 run\n");
    println!("| instance | matrices | rows | nonzeros | longest row | uncut clauses for it | cut-4 clauses | cut-4 clauses per nonzero |");
    println!("|---|---|---|---|---|---|---|---|");
    macro_rules! mq {
        ($n:literal) => {{
            let (system, _) = planted::<$n>(220, $n, 0, 0.5);
            let system = with_field_equations(&system).expect("GF(2) has an order");
            matrix_clause_report(
                &format!("MQ n={} m={}", $n, $n),
                &macaulay_matrices(&system),
            );
        }};
    }
    mq!(8);
    mq!(10);
    mq!(12);
    mq!(14);
}

// --- replay ----------------------------------------------------------------------------------

struct Xor {
    variables: usize,
    rows: Vec<(bool, Vec<usize>)>,
}

/// The constant column becomes the right-hand side; every other column is a variable.
fn export<const N: usize>(macaulay: &MacaulayMatrix<N, Zp2>) -> Xor {
    let constant = macaulay.columns().iter().position(Monomial::is_one);
    let index = |column: usize| match constant {
        Some(c) if column > c => column - 1,
        _ => column,
    };
    let rows = macaulay
        .matrix()
        .rows()
        .iter()
        .map(|row| {
            let mut rhs = false;
            let mut variables = Vec::with_capacity(row.nonzeros());
            for &(column, _) in row.entries() {
                if Some(column) == constant {
                    rhs = true;
                } else {
                    variables.push(index(column));
                }
            }
            (rhs, variables)
        })
        .collect();
    Xor {
        variables: macaulay.num_columns() - usize::from(constant.is_some()),
        rows,
    }
}

fn xor_text(xor: &Xor) -> String {
    let mut text = format!("p xor {} {}\n", xor.variables, xor.rows.len());
    for (rhs, variables) in &xor.rows {
        text.push_str(if *rhs { "1" } else { "0" });
        for v in variables {
            text.push(' ');
            text.push_str(&v.to_string());
        }
        text.push('\n');
    }
    text
}

struct DriverRun {
    sat: bool,
    solve: Duration,
    rank: Option<usize>,
    dimension: Option<usize>,
}

fn cms(driver: &Path, file: &Path, gauss: bool, dimension: bool) -> DriverRun {
    let mut command = Command::new(driver);
    command.args(["--max-time", "30"]);
    if !gauss {
        command.arg("--no-gauss");
    }
    if dimension {
        command.arg("--dimension");
    }
    let output = command.arg(file).output().expect("cms-xor-driver runs");
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "cms-xor-driver failed on {}: {text}",
        file.display()
    );
    let field = |key: &str| {
        text.lines()
            .find_map(|l| l.strip_prefix(key)?.strip_prefix(' ').map(str::to_owned))
    };
    DriverRun {
        sat: field("status").as_deref() == Some("sat"),
        solve: Duration::from_nanos(field("solve_ns").expect("solve_ns").parse().unwrap()),
        rank: field("rank").map(|v| v.parse().unwrap()),
        dimension: field("dimension").map(|v| v.parse().unwrap()),
    }
}

const BACKENDS: [Backend; 3] = [Backend::Dense, Backend::Sparse, Backend::Adaptive];

struct Replayed {
    shape: (usize, usize, usize),
    rank: usize,
    dimension: usize,
    row_operations: usize,
    peak: usize,
    row_xors: usize,
    backends: [Duration; 3],
    pack: Duration,
    packed: Duration,
    export: Duration,
    cms_gauss: Option<Duration>,
    cms_plain: Option<Duration>,
}

fn replay_matrix<const N: usize>(
    macaulay: &MacaulayMatrix<N, Zp2>,
    reps: usize,
    driver: Option<&Path>,
    file: &Path,
) -> Replayed {
    let matrix = macaulay.matrix();
    let mut backends = [Duration::MAX; 3];
    let (mut pack, mut packed, mut export_time) = (Duration::MAX, Duration::MAX, Duration::MAX);
    let mut reference = None;
    let mut row_xors = 0;
    for rep in 0..reps {
        for offset in 0..BACKENDS.len() {
            let slot = (rep + offset) % BACKENDS.len();
            let mut working = matrix.clone();
            let start = Instant::now();
            let statistics = row_echelon_with(BACKENDS[slot], &mut working, usize::MAX)
                .expect("an unbounded budget cannot refuse");
            backends[slot] = backends[slot].min(start.elapsed());
            match &reference {
                None => reference = Some((working, statistics)),
                Some((m, s)) => {
                    assert_eq!(&working, m, "{:?} disagreed on the matrix", BACKENDS[slot]);
                    assert_eq!(
                        &statistics, s,
                        "{:?} disagreed on the counters",
                        BACKENDS[slot]
                    );
                }
            }
        }
        let start = Instant::now();
        let mut bits = BitMatrix::from_sparse(matrix);
        pack = pack.min(start.elapsed());
        let start = Instant::now();
        let statistics = reduced_row_echelon_packed(&mut bits);
        packed = packed.min(start.elapsed());
        row_xors = statistics.row_xors;
        let (_, s) = reference.as_ref().expect("set above");
        assert_eq!(statistics.rank, s.rank, "packed and sparse ranks differ");

        let start = Instant::now();
        let text = xor_text(&export(macaulay));
        export_time = export_time.min(start.elapsed());
        if rep == 0 {
            fs::write(file, text).expect("write the XOR file");
        }
    }
    let (_, statistics) = reference.expect("at least one repetition");
    let rank = statistics.rank;
    let dimension = export(macaulay).variables - rank;

    // The independent check comes before any CMS time is kept.
    let (mut cms_gauss, mut cms_plain) = (None, None);
    if let Some(driver) = driver {
        let checked = cms(driver, file, true, true);
        assert!(
            checked.sat,
            "a planted system's linearization is consistent"
        );
        assert_eq!(checked.rank, Some(rank), "CMS and Zeebra disagree on rank");
        assert_eq!(
            checked.dimension,
            Some(dimension),
            "CMS and Zeebra disagree on dimension"
        );
        let mut best = Duration::MAX;
        for _ in 0..reps {
            best = best.min(cms(driver, file, true, false).solve);
        }
        cms_gauss = Some(best);
        let plain = cms(driver, file, false, false);
        assert!(plain.sat, "Gauss-off CMS must agree on satisfiability");
        cms_plain = Some(plain.solve);
    }
    Replayed {
        shape: (matrix.num_rows(), matrix.num_columns(), matrix.nonzeros()),
        rank,
        dimension,
        row_operations: statistics.row_operations,
        peak: statistics.peak_nonzeros,
        row_xors,
        backends,
        pack,
        packed,
        export: export_time,
        cms_gauss,
        cms_plain,
    }
}

fn replay_instance<const N: usize>(reps: usize, driver: Option<&Path>, dir: &Path) {
    let (system, _) = planted::<N>(220, N, 0, 0.5);
    let system = with_field_equations(&system).expect("GF(2) has an order");
    let shown = |d: Option<Duration>| d.map_or("not run".into(), |d| format!("{:.0}", micros(d)));
    for (index, macaulay) in macaulay_matrices(&system).iter().enumerate() {
        let file = dir.join(format!("mq{N}-{index}.xor"));
        let r = replay_matrix(macaulay, reps, driver, &file);
        let per_op = |d: Duration| d.as_nanos() as f64 / r.row_operations.max(1) as f64;
        println!(
            "| n={N} #{index} | {}x{} | {} | {} | {} | {} | {} | {} | {:.0} | {:.0} | {:.0} | {:.1} | {:.1} | {:.0} + {:.0} | {:.0} | {} | {} |",
            r.shape.0,
            r.shape.1,
            r.shape.2,
            r.rank,
            r.dimension,
            r.row_operations,
            r.row_xors,
            r.peak,
            micros(r.backends[0]),
            micros(r.backends[1]),
            micros(r.backends[2]),
            per_op(r.backends[1]),
            per_op(r.backends[2]),
            micros(r.pack),
            micros(r.packed),
            micros(r.export),
            shown(r.cms_gauss),
            shown(r.cms_plain),
        );
    }
}

fn replay(reps: usize) {
    let driver = ext_bin("cms-xor-driver", "ZEEBRA_CMS_XOR_DRIVER");
    let dir = scratch();
    match &driver {
        Some(d) => println!(
            "CMS driver: {}; rank and dimension asserted equal per matrix\n",
            d.display()
        ),
        None => println!("no cms-xor-driver found (ZEEBRA_EXT_PREFIX); CMS columns not run\n"),
    }
    println!("Microseconds, minimum of {reps}; CMS is its first solve() only, in-process.\n");
    println!("| matrix | rows x cols | nonzeros | rank | dimension | row ops | packed row xors | peak live | Dense | Sparse | Adaptive | Sparse ns/op | Adaptive ns/op | packed: pack + RREF | XOR export | CMS Gauss | CMS no Gauss |");
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|");
    replay_instance::<8>(reps, driver.as_deref(), &dir);
    replay_instance::<10>(reps, driver.as_deref(), &dir);
    replay_instance::<12>(reps, driver.as_deref(), &dir);
    replay_instance::<14>(reps, driver.as_deref(), &dir);
    let _ = fs::remove_dir_all(&dir);
}

// --- preprocess ------------------------------------------------------------------------------

/// kissat's model as `x_i` for `i < variables`; `None` when it reports unsatisfiable.
fn kissat(
    binary: &Path,
    cnf: &Cnf,
    file: &Path,
    variables: usize,
) -> (Option<Vec<bool>>, Duration) {
    fs::write(file, cnf.dimacs()).expect("write the CNF");
    let start = Instant::now();
    let output = Command::new(binary)
        .arg("-q")
        .arg(file)
        .output()
        .expect("kissat runs");
    let elapsed = start.elapsed();
    match output.status.code() {
        Some(10) => {}
        Some(20) => return (None, elapsed),
        other => panic!("kissat exited with {other:?}"),
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut model = vec![false; variables];
    for literal in text
        .lines()
        .filter_map(|l| l.strip_prefix("v "))
        .flat_map(str::split_whitespace)
    {
        let literal: i64 = literal.parse().expect("a DIMACS literal");
        let v = literal.unsigned_abs() as usize;
        if (1..=variables).contains(&v) {
            model[v - 1] = literal > 0;
        }
    }
    (Some(model), elapsed)
}

fn point<const N: usize>(bits: &[bool]) -> [Zp2; N] {
    std::array::from_fn(|i| if bits[i] { Zp2::one() } else { Zp2::zero() })
}

fn vanishes<const N: usize>(system: &[MultivariatePolynomial<N, Zp2>], x: &[Zp2; N]) -> bool {
    system.iter().all(|p| p.eval(x).is_zero())
}

fn preprocess_instance<const N: usize, const M: usize>(
    seed: u64,
    reps: usize,
    kissat_bin: &Path,
    dir: &Path,
    run_f4: bool,
) {
    let affine = N - M;
    let (system, plant) = planted::<N>(seed, M, affine, 0.5);
    assert!(vanishes(&system, &plant));

    let start = Instant::now();
    let (remaining, record) = eliminate_affine(&system);
    let projected = record
        .project::<M>(&remaining)
        .expect("each affine form removes a variable");
    let eliminate = start.elapsed();

    let original_cnf = encode(&system.iter().map(anf).collect::<Vec<_>>(), N, 4);
    let projected_cnf = encode(&projected.iter().map(anf).collect::<Vec<_>>(), M, 4);
    let original_file = dir.join(format!("orig-{N}-{seed}.cnf"));
    let projected_file = dir.join(format!("proj-{N}-{seed}.cnf"));

    let (mut alone, mut after) = (Duration::MAX, Duration::MAX);
    for rep in 0..reps {
        for arm in [rep % 2, 1 - rep % 2] {
            if arm == 0 {
                let (model, t) = kissat(kissat_bin, &original_cnf, &original_file, N);
                let x = point::<N>(&model.expect("the plant is a solution"));
                assert!(
                    vanishes(&system, &x),
                    "kissat's model fails the original system"
                );
                alone = alone.min(t);
            } else {
                let (model, t) = kissat(kissat_bin, &projected_cnf, &projected_file, M);
                let lifted = record
                    .lift(&point::<M>(&model.expect("the projection keeps the plant")))
                    .expect("M kept variables");
                assert!(
                    vanishes(&system, &lifted),
                    "the lifted model fails the original system"
                );
                after = after.min(t);
            }
        }
    }

    let timed = |run: &dyn Fn() -> bool| {
        if !run_f4 {
            return "not run".to_string();
        }
        let start = Instant::now();
        assert!(run(), "solve_one's point fails the original system");
        format!("{:.1}", millis(start.elapsed()))
    };
    let f4_alone = timed(&|| {
        let closed = with_field_equations(&system).expect("GF(2) has an order");
        let mut rng = StdRng::seed_from_u64(seed);
        let x = solve_one(&closed, &mut rng)
            .expect("solvable")
            .expect("a point");
        vanishes(&system, &x)
    });
    let f4_after = timed(&|| {
        let closed = with_field_equations(&projected).expect("GF(2) has an order");
        let mut rng = StdRng::seed_from_u64(seed);
        let x = solve_one(&closed, &mut rng)
            .expect("solvable")
            .expect("a point");
        vanishes(&system, &record.lift(&x).expect("M kept variables"))
    });

    println!(
        "| n={N}: {M} quadratics + {affine} affine, seed {seed} | {} / {} | {} / {} | {:.1} | {:.1} | {:.2} | {:.2} | {f4_alone} | {f4_after} |",
        original_cnf.clauses.len(),
        original_cnf.variables,
        projected_cnf.clauses.len(),
        projected_cnf.variables,
        millis(alone),
        millis(after + eliminate),
        millis(eliminate),
        (after + eliminate).as_secs_f64() / alone.as_secs_f64(),
    );
}

fn preprocess(reps: usize) {
    let Some(kissat_bin) = ext_bin("kissat", "ZEEBRA_KISSAT") else {
        println!("no kissat found (ZEEBRA_EXT_PREFIX or ZEEBRA_KISSAT); nothing measured");
        return;
    };
    let dir = scratch();
    println!(
        "kissat: {}; every model checked against the original system\n",
        kissat_bin.display()
    );
    println!("Wall milliseconds, minimum of {reps}, one kissat process per run; CNF cut at 4.\n");
    println!("| instance | CNF clauses / vars | after elimination | kissat alone | eliminate + kissat | of which eliminate | ratio | F4 solve_one alone | F4 after elimination |");
    println!("|---|---|---|---|---|---|---|---|---|");
    for seed in [1u64, 2, 3] {
        preprocess_instance::<16, 12>(seed, reps, &kissat_bin, &dir, true);
    }
    for seed in [1u64, 2, 3] {
        preprocess_instance::<24, 18>(seed, reps, &kissat_bin, &dir, false);
    }
    for seed in [1u64, 2, 3] {
        preprocess_instance::<28, 21>(seed, reps, &kissat_bin, &dir, false);
    }
    let _ = fs::remove_dir_all(&dir);
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let reps = args.get(1).and_then(|r| r.parse().ok()).unwrap_or(3);
    match args.first().map(String::as_str) {
        Some("clauses") => clauses(),
        Some("replay") => replay(reps),
        Some("preprocess") => preprocess(reps),
        _ => {
            eprintln!("usage: sat_algebra clauses | replay [reps] | preprocess [reps]");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn polynomial<const N: usize>(terms: &[&[u32]]) -> MultivariatePolynomial<N, Zp2> {
        let terms: Vec<_> = terms
            .iter()
            .map(|e| (Monomial::new(e), Zp2::one()))
            .collect();
        MultivariatePolynomial::new(&terms)
    }

    fn satisfied(cnf: &Cnf, assignment: u64) -> bool {
        cnf.clauses.iter().all(|clause| {
            clause.iter().any(|&literal| {
                let value = assignment >> (literal.unsigned_abs() - 1) & 1 == 1;
                value == (literal > 0)
            })
        })
    }

    /// Squares collapse and repeated monomials cancel, because both are identities on {0,1}.
    #[test]
    fn anf_is_multilinear_and_cancels_in_pairs() {
        let p = polynomial::<3>(&[&[2, 0, 0], &[1, 0, 0], &[1, 1, 0], &[0, 0, 0]]);
        assert_eq!(
            anf(&p),
            Anf {
                monomials: [0b011].into_iter().collect(),
                constant: true
            }
        );
    }

    /// An XOR of length k costs 2^(k-1) clauses uncut, and cutting trades clauses for variables.
    #[test]
    fn xor_cost_matches_the_closed_forms() {
        assert_eq!(xor_cost(5, 64), (16, 0));
        assert_eq!(xor_cost(4, 4), (8, 0));
        // 6 = 3 + aux, then aux + 3: two chunks of length 4.
        assert_eq!(xor_cost(6, 4), (16, 1));
    }

    /// The encoding is satisfiable over an x-assignment exactly when every equation holds there.
    #[test]
    fn encoding_preserves_the_boolean_solution_set() {
        let system = [
            polynomial::<4>(&[&[1, 1, 0, 0], &[0, 0, 1, 1], &[1, 0, 0, 0], &[0, 0, 0, 0]]),
            polynomial::<4>(&[&[1, 0, 1, 0], &[0, 1, 0, 1], &[0, 1, 1, 0], &[0, 0, 0, 1]]),
        ];
        let system: Vec<Anf> = system.iter().map(anf).collect();
        for cut in [3, 4, 64] {
            let cnf = encode(&system, 4, cut);
            assert!(cnf.variables <= 20, "brute force needs a small encoding");
            let mut projected = BTreeSet::new();
            for assignment in 0..1u64 << cnf.variables {
                if satisfied(&cnf, assignment) {
                    projected.insert(assignment & 0b1111);
                }
            }
            let expected: BTreeSet<u64> = (0..16)
                .filter(|&x| system.iter().all(|e| holds(e, x)))
                .collect();
            assert_eq!(projected, expected, "cut {cut}");
        }
    }

    /// The emitted clause count is the Tseitin cost plus the closed-form XOR cost.
    #[test]
    fn encoding_size_matches_the_accounting() {
        let system = [anf(&polynomial::<6>(&[
            &[1, 1, 0, 0, 0, 0],
            &[0, 1, 1, 0, 0, 0],
            &[0, 0, 0, 1, 1, 1],
            &[1, 0, 0, 0, 0, 0],
            &[0, 0, 0, 0, 0, 1],
            &[0, 0, 1, 0, 0, 0],
        ]))];
        let cnf = encode(&system, 6, 4);
        // Tseitin: two degree-2 ANDs (3 clauses each), one degree-3 AND (4 clauses).
        let (xor_clauses, aux) = xor_cost(6, 4);
        assert_eq!(cnf.clauses.len() as u64, 3 + 3 + 4 + xor_clauses);
        assert_eq!(cnf.variables as u64, 6 + 3 + aux);
    }

    /// Every exported Macaulay row holds at the plant's monomial values, with the constant column
    /// read as the right-hand side.
    #[test]
    fn exported_matrices_are_satisfied_by_the_plant() {
        let (system, plant) = planted::<5>(7, 5, 0, 0.5);
        let system = with_field_equations(&system).expect("GF(2) has an order");
        let matrices = macaulay_matrices(&system);
        assert!(!matrices.is_empty());
        for macaulay in &matrices {
            let values: Vec<bool> = macaulay
                .columns()
                .iter()
                .filter(|m| !m.is_one())
                .map(|m| !m.eval(&plant).is_zero())
                .collect();
            let xor = export(macaulay);
            assert_eq!(xor.variables, values.len());
            for (rhs, variables) in &xor.rows {
                let parity = variables.iter().filter(|&&v| values[v]).count() % 2 == 1;
                assert_eq!(parity, *rhs);
            }
        }
    }

    /// Affine elimination keeps the plant: projecting it and lifting back recovers a root.
    #[test]
    fn affine_projection_lifts_back_to_a_root() {
        let (system, plant) = planted::<6>(3, 4, 2, 0.5);
        let (remaining, record) = eliminate_affine(&system);
        let projected = record.project::<4>(&remaining).expect("two affine forms");
        let kept = record.kept();
        let short: [Zp2; 4] = std::array::from_fn(|i| plant[kept[i]]);
        assert!(vanishes(&projected, &short));
        assert!(vanishes(&system, &record.lift(&short).expect("four kept")));
    }
}
