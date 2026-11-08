//! Where the matrix interreduction route's memory goes, and whether the budget can see it.
//!
//! `examples/interreduction_routes.rs` compares the two routes' *wall times*. This measures the
//! one quantity #536 is about: the nonzero entries **live at once during elimination**, which the
//! route's budgets did not test and which turned out to be where the 13.1 GB on `katsura-11` was.
//!
//! One rung and one arm per process, because peak resident size is a per-process reading and two
//! arms in one process would report the larger of them twice:
//!
//! ```text
//! cargo run --release --example interreduce_working_set -- katsura-11 --arm unbounded
//! cargo run --release --example interreduce_working_set -- katsura-11 --arm default
//! cargo run --release --example interreduce_working_set -- katsura-8 --arm division
//! ```
//!
//! - `unbounded` lifts the live-entry allowance clear of the pass, so the elimination runs to
//!   completion and *reports its own high-water mark*. That is the attribution: the figure is
//!   counted by the elimination rather than inferred from the matrix's shape, which is the quantity
//!   that already looked fine.
//! - `default` is the shipped allowance, where the pass refuses and falls back.
//! - `division` is the comparand the memory ratio is against.

use std::time::{Duration, Instant};

use zeebra::{
    fields::Zp2147483647,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_reported, F4Options, F4Statistics, InterreductionRoute, MatrixRefusal,
    },
    util::{isa_floor, peak_resident_bytes},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type F = Zp2147483647;

/// Bytes a live sparse entry occupies: a column index and a field element.
fn bytes_per_entry<G: FiniteField>() -> usize {
    size_of::<(usize, G)>()
}

fn mb(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

/// Which budget configuration to run under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Arm {
    /// The matrix route with the live-entry allowance lifted, so elimination reports its own peak.
    Unbounded,
    /// The matrix route at the shipped allowance.
    Default,
    /// The division route, which is what the memory ratio is against.
    Division,
}

fn options(arm: Arm, wall: Option<Duration>) -> F4Options {
    let mut options = F4Options {
        measure_stages: true,
        interreduction: if arm == Arm::Division {
            InterreductionRoute::Division
        } else {
            InterreductionRoute::Matrix
        },
        max_wall_time: wall,
        ..F4Options::default()
    };
    if arm == Arm::Unbounded {
        // Both halves of the coupled pair, because `live_entry_allowance` is their `min` and
        // lifting one alone moves nothing (#322).
        options.max_live_nonzeros = usize::MAX;
        options.max_live_bytes = usize::MAX;
    }
    options
}

/// Print what the matrix pass did, in the units the budget is stated in.
fn emit(label: &str, arm: Arm, statistics: &F4Statistics, elapsed: Duration, elements: usize) {
    let entry = bytes_per_entry::<F>();
    println!(
        "- {label}, {arm:?}: {:.1} ms, basis {} elements, VmHWM {:.1} MB",
        elapsed.as_secs_f64() * 1e3,
        elements,
        mb(peak_resident_bytes().unwrap_or(0) as usize)
    );
    println!(
        "  interreduction stage {:.1} ms",
        statistics.stages.interreduction.as_secs_f64() * 1e3
    );
    // The batch loop's own high-water mark, which the same allowance has always bounded. Printed
    // beside the interreduction's so the two are comparable: if the stage's working set is the
    // larger of the two, a budget the loop never approaches is not protecting the computation.
    println!(
        "  batch loop high-water {} live entries ({:.1} MB), over {} batches",
        statistics.max_live_nonzeros,
        mb(statistics.max_live_nonzeros * entry),
        statistics.batches
    );
    match &statistics.interreduction_matrix {
        None => println!("  no matrix interreduction recorded (division route)"),
        Some(matrix) => {
            println!(
                "  matrix {} x {}, built {} entries ({:.1} MB), elements {}",
                matrix.rows,
                matrix.columns,
                matrix.nonzeros,
                mb(matrix.nonzeros * entry),
                matrix.elements
            );
            println!(
                "  elimination high-water {} live entries ({:.1} MB at {} B an entry) = {:.1}x the \
                 entries it was built with",
                matrix.peak_nonzeros,
                mb(matrix.peak_nonzeros * entry),
                entry,
                matrix.peak_nonzeros as f64 / matrix.nonzeros.max(1) as f64
            );
            println!(
                "  of which allocated {} entries ({:.1} MB) = {:.2}x the payload, the buffers the \
                 merge grew and nothing shrank",
                matrix.peak_entry_capacity,
                mb(matrix.peak_entry_capacity * entry),
                matrix.peak_entry_capacity as f64 / matrix.peak_nonzeros.max(1) as f64
            );
            match matrix.refused_by {
                None => println!("  the pass ran: fell_back = {}", matrix.fell_back),
                Some(MatrixRefusal::Rows { limit }) => {
                    println!("  REFUSED on rows > {limit}, fell back to division")
                }
                Some(MatrixRefusal::Columns { limit }) => {
                    println!("  REFUSED on columns > {limit}, fell back to division")
                }
                Some(MatrixRefusal::Nonzeros { nonzeros }) => {
                    println!(
                        "  REFUSED on {nonzeros} entries at construction, fell back to division"
                    )
                }
                Some(MatrixRefusal::LiveEntries { nonzeros }) => println!(
                    "  REFUSED on {nonzeros} live entries ({:.1} MB) during elimination, fell back \
                     to division",
                    mb(nonzeros * entry)
                ),
            }
        }
    }
}

/// Run one system under one arm, printing the row before anything else allocates.
fn run<const N: usize>(
    label: &str,
    system: &[MultivariatePolynomial<N, F>],
    arm: Arm,
    order: MonomialOrder,
    wall: Option<Duration>,
) {
    let options = options(arm, wall);
    print!("{}", options.budget_report::<F>());
    let start = Instant::now();
    let (basis, statistics) = f4_reported(system, order, &options);
    let elapsed = start.elapsed();
    match basis {
        Ok(basis) => emit(label, arm, &statistics, elapsed, basis.len()),
        Err(stopped) => {
            println!("- {label}, {arm:?}: stopped ({stopped})");
            emit(label, arm, &statistics, elapsed, 0);
        }
    }
}

fn main() {
    println!(
        "# #536: the matrix interreduction route's working set\n\n- built for {}",
        isa_floor()
    );

    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let value = |name: &str| {
        arguments
            .iter()
            .position(|a| a == name)
            .and_then(|at| arguments.get(at + 1))
            .cloned()
    };
    let arm = match value("--arm").as_deref() {
        Some("unbounded") => Arm::Unbounded,
        Some("division") => Arm::Division,
        None | Some("default") => Arm::Default,
        Some(other) => {
            eprintln!("--arm is unbounded, default or division, not {other}");
            return;
        }
    };
    let order = match value("--order").as_deref() {
        None | Some("grevlex") => MonomialOrder::GradedReverseLexicographic,
        Some("grlex") => MonomialOrder::GradedLexicographic,
        Some("lex") => MonomialOrder::Lexicographic,
        Some(other) => {
            eprintln!("--order is grevlex, grlex or lex, not {other}");
            return;
        }
    };
    let wall = value("--wall")
        .and_then(|s| s.parse().ok())
        .map(Duration::from_secs);
    let rung = arguments
        .iter()
        .find(|a| {
            !a.starts_with("--")
                && !matches!(
                    a.as_str(),
                    "unbounded" | "default" | "division" | "grevlex" | "grlex" | "lex"
                )
        })
        .cloned()
        .unwrap_or_else(|| "katsura-8".to_string());

    println!("- rung {rung}, {order:?}, arm {arm:?}, wall {wall:?}\n");

    match rung.as_str() {
        "katsura-6" => run("katsura-6", &katsura::<6, F>(), arm, order, wall),
        "katsura-7" => run("katsura-7", &katsura::<7, F>(), arm, order, wall),
        "katsura-8" => run("katsura-8", &katsura::<8, F>(), arm, order, wall),
        "katsura-9" => run("katsura-9", &katsura::<9, F>(), arm, order, wall),
        "katsura-10" => run("katsura-10", &katsura::<10, F>(), arm, order, wall),
        "katsura-11" => run("katsura-11", &katsura::<11, F>(), arm, order, wall),
        "cyclic-6" => run("cyclic-6", &cyclic::<6, F>(), arm, order, wall),
        "cyclic-7" => run("cyclic-7", &cyclic::<7, F>(), arm, order, wall),
        other => eprintln!("{other} is not a rung this example compiles"),
    }
}
