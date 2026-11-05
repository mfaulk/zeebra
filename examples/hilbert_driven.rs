//! What a Hilbert-driven cap is worth, against a cap chosen without one — and what certifying costs.
//!
//! M22-C. Four things are measured on each instance, and keeping them apart is the whole point:
//!
//! 1. the **baseline**, uncapped;
//! 2. **fixed caps**, which M22-A measured at 3.6x on Fukuoka type III `n=10` with no prediction
//!    and no certification at all;
//! 3. the **Hilbert-driven cap**, at several slacks, and the deferring variant;
//! 4. every row again with **`certify` on**, so the plan's §8.5 comparison — total cost *including*
//!    the check — is the one that decides anything.
//!
//! The second row is the reference that matters. A Hilbert-driven strategy that beats the uncapped
//! baseline has established nothing if a fixed cap of 64 beats it too: M22-B measured the
//! Hilbert-derived quota at the degree that matters on Fukuoka `n=10` as **65**, within one pair of
//! a number picked without any model.
//!
//! ```text
//! tools/fetch-mq-challenge.sh                      # for the MQ rows
//! cargo run --release --example hilbert_driven
//! cargo run --release --example hilbert_driven -- list
//! cargo run --release --example hilbert_driven -- mq3-n15
//! ```
//!
//! Every row's basis is asserted equal to the baseline's. A cap discards no pair — a capped batch
//! leaves the rest pending and a deferred degree is promoted back — so a differing basis would be a
//! defect, and reporting it in a column rather than failing would bury it.

use std::{path::PathBuf, time::Instant};

use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_with_options,
        research::{CicoInstance, MqInstance, Poseidon, PoseidonParameters, KOALABEAR_PRIME},
        F4Options, F4Statistics, HilbertSelection,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Q = PrimeFieldElement64<31>;
type K = PrimeFieldElement64<KOALABEAR_PRIME>;
type P = PrimeFieldElement64<2_147_483_647>;

const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const C1: u64 = 0xC0_9DE4;

/// The configurations compared, in the order the tables print them.
///
/// `(label, max_pairs_per_batch, hilbert)`. The fixed caps come before the Hilbert-driven ones
/// deliberately: they are the reference, not the control group.
fn configurations() -> Vec<(String, Option<usize>, HilbertSelection)> {
    let mut out: Vec<(String, Option<usize>, HilbertSelection)> =
        vec![("uncapped".to_string(), None, HilbertSelection::Off)];
    for cap in [256usize, 64, 16] {
        out.push((
            format!("fixed cap {}", cap),
            Some(cap),
            HilbertSelection::Off,
        ));
    }
    out.push(("observe".to_string(), None, HilbertSelection::Observe));
    for slack in [0usize, 4, 16] {
        out.push((
            format!("hilbert limited+{}", slack),
            None,
            HilbertSelection::CertifiedLimited { slack },
        ));
    }
    for slack in [0usize, 4] {
        out.push((
            format!("hilbert deferred+{}", slack),
            None,
            HilbertSelection::Deferred { slack },
        ));
    }
    out
}

/// The resource policy, stated once.
fn options(cap: Option<usize>, hilbert: HilbertSelection, certify: bool) -> F4Options {
    F4Options {
        max_pairs_per_batch: cap,
        hilbert,
        certify,
        profile_degrees: true,
        max_matrix_columns: 60_000,
        max_live_bytes: 400_000_000,
        max_batches: Some(20_000),
        ..F4Options::default()
    }
}

/// One measured configuration.
struct Row {
    label: String,
    pairs_reduced: usize,
    batches: usize,
    withheld: usize,
    deferred: usize,
    max_columns: usize,
    peak_entries: usize,
    solve_millis: f64,
    certify_millis: f64,
    predicted: i128,
    observed: usize,
    outcome: String,
}

impl Row {
    /// Solve plus certification, which is the only figure a production comparison may use.
    fn total_millis(&self) -> f64 {
        self.solve_millis + self.certify_millis
    }
}

fn header() {
    println!(
        "| {:<22} | {:>6} | {:>5} | {:>6} | {:>6} | {:>7} | {:>9} | {:>8} | {:>8} | {:>8} | {:>11} |",
        "configuration",
        "pairs",
        "batch",
        "held",
        "defer",
        "cols",
        "peak",
        "solve ms",
        "cert ms",
        "total ms",
        "pred/obs"
    );
    println!(
        "|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|",
        "-".repeat(24),
        "-".repeat(8),
        "-".repeat(7),
        "-".repeat(8),
        "-".repeat(8),
        "-".repeat(9),
        "-".repeat(11),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(10),
        "-".repeat(13),
    );
}

fn print_row(row: &Row) {
    if !row.outcome.is_empty() {
        println!("| {:<22} | {} |", truncate(&row.label, 22), row.outcome);
        return;
    }
    println!(
        "| {:<22} | {:>6} | {:>5} | {:>6} | {:>6} | {:>7} | {:>9} | {:>8} | {:>8} | {:>8} | {:>11} |",
        truncate(&row.label, 22),
        row.pairs_reduced,
        row.batches,
        row.withheld,
        row.deferred,
        row.max_columns,
        row.peak_entries,
        format!("{:.1}", row.solve_millis),
        format!("{:.1}", row.certify_millis),
        format!("{:.1}", row.total_millis()),
        format!("{}/{}", row.predicted, row.observed),
    );
}

fn truncate(s: &str, width: usize) -> String {
    if s.chars().count() <= width {
        s.to_string()
    } else {
        format!("{}…", s.chars().take(width - 1).collect::<String>())
    }
}

fn measure(label: &str, statistics: &F4Statistics, solve: f64, certify: f64) -> Row {
    Row {
        label: label.to_string(),
        pairs_reduced: statistics.pairs_reduced,
        batches: statistics.batches,
        withheld: statistics.hilbert.pairs_withheld,
        deferred: statistics.hilbert.pairs_deferred,
        max_columns: statistics.max_matrix_columns,
        peak_entries: statistics.max_live_nonzeros,
        solve_millis: solve,
        certify_millis: certify,
        predicted: statistics.hilbert.predicted_new_elements,
        observed: statistics.hilbert.observed_new_elements,
        outcome: String::new(),
    }
}

/// Run one configuration twice — without and with certification — and assert the basis.
///
/// Twice rather than subtracting a reported duration from a total: the certification report's own
/// clock is the honest measure of the check, and running the solve separately keeps the "solve ms"
/// column comparable with every other table in this milestone, which was taken without the check.
fn attempt<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    label: &str,
    cap: Option<usize>,
    hilbert: HilbertSelection,
    reference: Option<&[MultivariatePolynomial<N, F>]>,
) -> Option<(Row, Vec<MultivariatePolynomial<N, F>>)> {
    let at = Instant::now();
    let result = f4_with_options(system, GREVLEX, &options(cap, hilbert, false));
    let solve = at.elapsed().as_secs_f64() * 1e3;

    let (basis, statistics) = match result {
        Ok(pair) => pair,
        Err(e) => {
            return Some((
                Row {
                    label: label.to_string(),
                    outcome: e.to_string(),
                    pairs_reduced: 0,
                    batches: 0,
                    withheld: 0,
                    deferred: 0,
                    max_columns: 0,
                    peak_entries: 0,
                    solve_millis: solve,
                    certify_millis: 0.0,
                    predicted: 0,
                    observed: 0,
                },
                Vec::new(),
            ));
        }
    };

    if let Some(reference) = reference {
        assert_eq!(
            basis, reference,
            "{}: a selection strategy changed the reduced Gröbner basis",
            label
        );
    }

    // The same configuration with the check on. A failure here is a defect, not a result.
    let (_, certified) = f4_with_options(system, GREVLEX, &options(cap, hilbert, true))
        .unwrap_or_else(|e| panic!("{}: certification refused the basis: {}", label, e));
    let certify = certified
        .certification
        .expect("certify was on")
        .elapsed
        .as_secs_f64()
        * 1e3;

    Some((measure(label, &statistics, solve, certify), basis))
}

fn instances() -> Vec<&'static str> {
    vec![
        "katsura-5",
        "katsura-6",
        "cyclic-5",
        "poseidon-t2-rf2-rp2",
        "poseidon-t2-rf4",
        "mq3-n10",
        "mq3-n15",
    ]
}

fn mq_directory() -> PathBuf {
    std::env::var("ZEEBRA_MQ_DIR")
        .unwrap_or_else(|_| "research/instances/mq".to_string())
        .into()
}

fn load_mq(stem: &str) -> Option<MqInstance> {
    let text = std::fs::read_to_string(mq_directory().join(stem)).ok()?;
    MqInstance::parse(&text).ok()
}

fn cico<const N: usize>(t: usize, r_f: usize, r_p: usize) -> Vec<MultivariatePolynomial<N, K>> {
    let poseidon = Poseidon::<K>::new(PoseidonParameters {
        prime: KOALABEAR_PRIME,
        alpha: 3,
        t,
        r_f,
        r_p,
    })
    .expect("R_F is even");
    let free: Vec<K> = (0..t - 1).map(|i| K::new(1_000 + i as u64)).collect();
    CicoInstance::planted(
        poseidon,
        1,
        &[K::new(C1)],
        &free,
        Some(PoseidonParameters::bounty_cico()),
    )
    .expect("the right widths")
    .system::<N>()
    .expect("the right dimension")
}

/// Every configuration on one system, with the baseline's basis as the reference.
macro_rules! sweep {
    ($system:expr) => {{
        let system = $system;
        let mut reference: Option<Vec<_>> = None;
        header();
        for (label, cap, hilbert) in configurations() {
            match attempt(&system, &label, cap, hilbert, reference.as_deref()) {
                None => {}
                Some((row, basis)) => {
                    if reference.is_none() && !basis.is_empty() {
                        reference = Some(basis);
                    }
                    print_row(&row);
                }
            }
        }
    }};
}

fn run_instance(name: &str) {
    println!("### {}", name);
    println!();
    match name {
        "katsura-5" => sweep!(katsura::<5, P>()),
        "katsura-6" => sweep!(katsura::<6, P>()),
        "cyclic-5" => sweep!(cyclic::<5, P>()),
        "poseidon-t2-rf2-rp2" => sweep!(cico::<7>(2, 2, 2)),
        "poseidon-t2-rf4" => sweep!(cico::<9>(2, 4, 0)),
        "mq3-n10" => match load_mq("ToyExample-type3-n10-seed0") {
            Some(instance) => sweep!(instance.system::<10, Q>().expect("ten variables")),
            None => println!("instance data absent; run `tools/fetch-mq-challenge.sh`."),
        },
        "mq3-n15" => match load_mq("ToyExample-type3-n15-seed0") {
            Some(instance) => sweep!(instance.system::<15, Q>().expect("fifteen variables")),
            None => println!("instance data absent; run `tools/fetch-mq-challenge.sh`."),
        },
        other => println!("unknown instance `{}`; `-- list` names them.", other),
    }
    println!();
}

fn main() {
    let argument = std::env::args().nth(1);
    if argument.as_deref() == Some("list") {
        println!("instances:");
        for name in instances() {
            println!("  {}", name);
        }
        return;
    }

    println!("# A Hilbert-driven cap, against a cap chosen without one");
    println!();
    println!(
        "Configuration: `F4Options::recommended()` with `profile_degrees`, \
         `max_matrix_columns = 60_000`, `max_live_bytes = 400 MB`, `max_batches = 20_000`, grevlex \
         throughout. Reproduce with `cargo run --release --example hilbert_driven`."
    );
    println!();
    println!(
        "`held` is pairs a cap left pending for a later batch at the same degree; `defer` is pairs \
         moved out of the pending set and promoted back later. `pred/obs` is the predicted count of \
         new leading monomials against the new basis elements the same degrees produced — **below \
         one means the prediction caps too hard**, above one means it is inert."
    );
    println!();
    println!(
        "**`total ms` is the only column a production decision may use.** A strategy that skips \
         work has to be compared on its cost including the check that establishes the result, which \
         is the plan's §8.5; `solve ms` is there so the two halves can be seen."
    );
    println!();
    println!(
        "Every row's basis is asserted equal to the uncapped baseline's, and every row is also run \
         with `certify` on and asserted to pass. Neither limiting mode discards a pair, so a \
         differing basis would be a defect."
    );
    println!();

    match argument {
        Some(name) => run_instance(&name),
        None => {
            for name in instances() {
                run_instance(name);
            }
        }
    }
}
