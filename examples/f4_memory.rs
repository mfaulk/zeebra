//! Where an F4 computation's memory goes, attributed to named structures by measurement.
//!
//! `examples/f4_profile.rs` says where the *time* goes. This says where the bytes go, and it
//! exists because the answer turned out not to be the matrix: on `fukuoka-mq-III-n20-seed0` the
//! entry budget accounts for 195 MB of a 14.75 GB peak — 1.3% — and
//! `docs/research/f4-resource-scaling.md` §5 could not say where the rest was.
//!
//! Two instruments, reported side by side, because neither alone would settle it:
//!
//! - a tracking `#[global_allocator]`, which gives the **peak live heap of a named stage** exactly,
//!   including the temporaries no counter knows about. `util::peak_resident_bytes` cannot do this:
//!   it is a process high-water mark, so it cannot say which stage raised it.
//! - the solver's own counters times `size_of`, which gives **a named structure's** share. The
//!   allocator cannot do this: it sees bytes, not which `Vec` they went to.
//!
//! The stages are measured on the real batches rather than on a reimplemented main loop: a
//! [`BatchObserver`] receives each batch as F4 selected it, and re-runs symbolic preprocessing and
//! matrix construction under the allocator before the library does them for real. That costs the
//! stages twice over in time and nothing in peak memory, since each copy is dropped before the
//! next allocation. **The last batch observed is the one that crosses the budget**, which is the
//! batch the attribution is about and the one no `F4Statistics` field describes — `reduce_batch_in`
//! has nothing to attach a refused batch's counters to.
//!
//! ```text
//! cargo run --release --example f4_memory                      # the benchmark systems
//! cargo run --release --example f4_memory -- katsura-7         # one of them
//! cargo run --release --example f4_memory -- mq <instance>     # a registered MQ instance
//! ```
//!
//! `ZEEBRA_MAX_ENTRIES` sets the live-entry cap, as `examples/scoreboard.rs` reads it, so a rung of
//! that ladder can be reproduced here with the attribution attached.

use std::{
    alloc::{GlobalAlloc, Layout, System},
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

use zeebra::{
    fields::{Zp2147483647, Zp31},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{
            macaulay::MacaulayMatrix,
            symbolic::{symbolic_preprocessing_with, MonicBasis, ReducerCache},
        },
        f4_observed_reported,
        research::mq::MqInstance,
        BatchObserver, CriticalPair, F4Options, F4Statistics,
    },
    util::peak_resident_bytes,
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

// === the allocator ===

/// Counts live heap bytes, so a stage's peak is exact rather than estimated.
struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

/// Record a growth of the live total, raising the peak if it is one.
fn grew(bytes: usize) {
    let live = LIVE.fetch_add(bytes, Ordering::Relaxed) + bytes;
    PEAK.fetch_max(live, Ordering::Relaxed);
}

unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = System.alloc(layout);
        if !pointer.is_null() {
            grew(layout.size());
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        System.dealloc(pointer, layout);
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let moved = System.realloc(pointer, layout, new_size);
        if !moved.is_null() {
            if new_size >= layout.size() {
                grew(new_size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - new_size, Ordering::Relaxed);
            }
        }
        moved
    }
}

#[global_allocator]
static ALLOCATOR: Tracking = Tracking;

/// Run `work`, returning its value, its wall time, and the peak live heap bytes it added.
///
/// Single-threaded by construction: the counters are process-wide, so a concurrent allocation
/// elsewhere would be attributed here. This binary spawns no threads.
fn measure<T>(work: impl FnOnce() -> T) -> (T, Duration, usize) {
    let baseline = LIVE.load(Ordering::Relaxed);
    PEAK.store(baseline, Ordering::Relaxed);
    let start = Instant::now();
    let value = work();
    let elapsed = start.elapsed();
    let peak = PEAK.load(Ordering::Relaxed).saturating_sub(baseline);
    (value, elapsed, peak)
}

// === the per-batch probe ===

/// What one batch's two allocating stages cost, measured.
#[derive(Clone, Copy, Debug, Default)]
struct BatchProbe {
    degree: u64,
    pairs: usize,
    basis_elements: usize,
    basis_terms: usize,

    /// Peak live heap of symbolic preprocessing, including the queue and the two monomial sets.
    symbolic_peak: usize,

    /// Rows the closure needed, or the row budget if it refused.
    rows: usize,

    /// Monomials enqueued before the deduplication test, and the queue's own high-water mark.
    monomials_enqueued: usize,
    max_pending_monomials: usize,

    /// Monomials actually tested, i.e. the size the `examined` set reached.
    divisor_queries: usize,

    /// Peak live heap of matrix construction, with the preprocessing result still live.
    construction_peak: usize,

    /// Columns and entries the matrix reached, or zero if construction refused.
    columns: usize,
    entries: usize,

    /// Whether either stage refused, and which.
    refused: Option<&'static str>,
}

/// Re-runs each batch's allocating stages under the tracking allocator, before F4 does them.
struct StageProbe<const N: usize> {
    options: F4Options,
    order: MonomialOrder,
    batches: Vec<BatchProbe>,

    /// Stop probing once a stage has refused: everything after it is F4 unwinding, and a probe
    /// there would measure the error path rather than a batch.
    done: bool,

    /// `N` is on the probe so the byte arithmetic can be done where `size_of::<Monomial<N>>()` is
    /// known. `PhantomData` would be the alternative and this is one line shorter.
    monomial_bytes: usize,
}

impl<const N: usize> StageProbe<N> {
    fn new(options: F4Options, order: MonomialOrder) -> Self {
        Self {
            options,
            order,
            batches: Vec::new(),
            done: false,
            monomial_bytes: size_of::<Monomial<N>>(),
        }
    }

    /// The batch whose symbolic preprocessing peaked highest.
    fn worst(&self) -> Option<&BatchProbe> {
        self.batches
            .iter()
            .max_by_key(|probe| probe.symbolic_peak.max(probe.construction_peak))
    }
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for StageProbe<N> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        if self.done {
            return;
        }
        let allowance = self.options.live_entry_allowance::<F>();
        let mut probe = BatchProbe {
            degree: pairs.iter().map(|pair| pair.degree).max().unwrap_or(0),
            pairs: pairs.len(),
            basis_elements: basis.len(),
            basis_terms: (0..basis.len()).map(|i| basis.element(i).terms.len()).sum(),
            ..BatchProbe::default()
        };

        // The same arguments `reduce_batch_in` passes, so this is the batch F4 is about to do and
        // not a differently budgeted approximation of it.
        let (preprocessed, _, symbolic_peak) = measure(|| {
            symbolic_preprocessing_with(
                basis,
                pairs,
                self.options.max_matrix_rows,
                self.options.reducer_selection,
                &mut ReducerCache::new(self.options.reducer_cache),
            )
        });
        probe.symbolic_peak = symbolic_peak;

        let preprocessed = match preprocessed {
            Ok(preprocessed) => preprocessed,
            Err(exceeded) => {
                probe.rows = exceeded.limit;
                probe.refused = Some("max_matrix_rows");
                self.done = true;
                self.batches.push(probe);
                return;
            }
        };
        probe.rows = preprocessed.rows.len();
        probe.monomials_enqueued = preprocessed.counts.monomials_enqueued;
        probe.max_pending_monomials = preprocessed.counts.max_pending_monomials;
        probe.divisor_queries = preprocessed.counts.divisor_queries;

        // Measured with `preprocessed` still live, as construction holds it: the figure wanted is
        // what the process adds on top of preprocessing, not what construction would cost alone.
        let (matrix, _, construction_peak) = measure(|| {
            MacaulayMatrix::build_within(
                basis,
                &preprocessed,
                self.order,
                self.options.max_matrix_columns,
                allowance,
            )
        });
        probe.construction_peak = construction_peak;
        match matrix {
            Ok(matrix) => {
                probe.columns = matrix.num_columns();
                probe.entries = matrix
                    .matrix()
                    .rows()
                    .iter()
                    .map(|row| row.nonzeros())
                    .sum();
            }
            Err(_) => {
                probe.refused = Some("entries or columns");
                self.done = true;
            }
        }
        self.batches.push(probe);
    }
}

// === the attribution ===

/// One named structure's measured share of a run's memory.
struct Site {
    name: &'static str,
    bytes: usize,
    method: String,
}

/// The structures the counters can price, largest first.
///
/// Every row is `count × size_of`, with the count taken from the solver's own counter and the size
/// from the type. That is an arithmetic **lower bound** on what the structure occupies: it is the
/// payload and excludes the slack a `HashMap`'s power-of-two capacity and a `Vec`'s doubling leave,
/// so the sum is expected to fall short of the allocator's measured peak rather than to match it.
/// The shortfall is reported as its own row instead of being distributed.
fn attribution<const N: usize>(
    statistics: &F4Statistics,
    worst: Option<&BatchProbe>,
    monomial_bytes: usize,
    pair_bytes: usize,
    pair_key_bytes: usize,
) -> Vec<Site> {
    let mut sites = Vec::new();

    if let Some(worst) = worst {
        sites.push(Site {
            name: "symbolic preprocessing, measured peak",
            bytes: worst.symbolic_peak,
            method: format!(
                "tracking allocator, batch at degree {} ({} rows)",
                worst.degree, worst.rows
            ),
        });
        sites.push(Site {
            name: "  of which: pending monomial queue",
            bytes: worst.max_pending_monomials * monomial_bytes,
            method: format!(
                "{} monomials at peak x {} B, VecDeque payload",
                worst.max_pending_monomials, monomial_bytes
            ),
        });
        sites.push(Site {
            name: "  of which: examined + covered sets",
            bytes: worst.divisor_queries * (monomial_bytes + 1) * 2,
            method: format!(
                "{} distinct monomials x ({} + 1) B x 2 sets",
                worst.divisor_queries, monomial_bytes
            ),
        });
        sites.push(Site {
            name: "  of which: preprocessed rows",
            bytes: worst.rows * (monomial_bytes + 2 * size_of::<usize>()),
            method: format!(
                "{} rows x PreprocessedRow<{}> = {} B",
                worst.rows,
                N,
                monomial_bytes + 2 * size_of::<usize>()
            ),
        });
        sites.push(Site {
            name: "matrix construction, measured peak",
            bytes: worst.construction_peak,
            method: format!(
                "tracking allocator, on top of preprocessing ({} columns, {} entries)",
                worst.columns, worst.entries
            ),
        });
    }

    sites.push(Site {
        name: "matrix entries (THE BUDGETED QUANTITY)",
        bytes: statistics.max_estimated_bytes,
        method: format!(
            "max_live_nonzeros {} x {} B + dense buffers {} B",
            statistics.max_live_nonzeros,
            statistics.bytes_per_entry,
            statistics.max_dense_buffer_bytes
        ),
    });
    sites.push(Site {
        name: "pair heap",
        bytes: statistics.peak_pair_queue.heap_entries * pair_bytes,
        method: format!(
            "{} heap entries x ScheduledPair<{}> = {} B",
            statistics.peak_pair_queue.heap_entries, N, pair_bytes
        ),
    });
    sites.push(Site {
        name: "pair criteria sets",
        bytes: statistics.peak_pair_queue.criteria_keys() * pair_key_bytes,
        method: format!(
            "{} keys x {} B, monotonically growing",
            statistics.peak_pair_queue.criteria_keys(),
            pair_key_bytes
        ),
    });
    sites.push(Site {
        name: "basis, stored twice",
        bytes: statistics.peak_basis_terms * (monomial_bytes + 8) * 2,
        method: format!(
            "{} terms x ({} + 8) B x 2 copies (Vec<Multivariate> and MonicBasis)",
            statistics.peak_basis_terms, monomial_bytes
        ),
    });

    sites
}

/// A markdown table rule: a dashed cell of each given width, pipe-separated.
fn rule(widths: &[usize]) -> String {
    let mut line = String::from("|");
    for width in widths {
        line.push_str(&"-".repeat(*width));
        line.push('|');
    }
    line
}

/// Megabytes, to one decimal, for a table cell.
fn mb(bytes: usize) -> String {
    format!("{:.1}", bytes as f64 / (1024.0 * 1024.0))
}

/// Run one system and print its attribution.
fn report<const N: usize, F: FiniteField>(
    label: &str,
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) {
    let mut probe: StageProbe<N> = StageProbe::new(options.clone(), order);
    let before_rss = peak_resident_bytes().unwrap_or(0);
    let ((result, statistics), elapsed, run_peak) =
        measure(|| f4_observed_reported(system, order, options, &mut probe));
    let after_rss = peak_resident_bytes().unwrap_or(0);

    println!(
        "\n## {} ({} variables, {} generators)",
        label,
        N,
        system.len()
    );
    match &result {
        Ok(basis) => println!(
            "- finished in {:.1} s with {} basis elements",
            elapsed.as_secs_f64(),
            basis.len()
        ),
        Err(error) => println!(
            "- stopped in {:.1} s: {} ({}, {:?})",
            elapsed.as_secs_f64(),
            error,
            error.limit_name(),
            error.stop_kind()
        ),
    }
    println!(
        "- batches {}, basis at peak {} elements / {} terms, pair heap at peak {} entries",
        statistics.batches,
        statistics.peak_basis_elements,
        statistics.peak_basis_terms,
        statistics.peak_pair_queue.heap_entries
    );
    println!(
        "- peak live heap during the run {} MB; process VmHWM {} MB before, {} MB after",
        mb(run_peak),
        mb(before_rss as usize),
        mb(after_rss as usize)
    );

    if let Some(worst) = probe.worst() {
        println!(
            "- the heaviest batch: degree {}, {} pairs against a basis of {} elements / {} terms{}",
            worst.degree,
            worst.pairs,
            worst.basis_elements,
            worst.basis_terms,
            match worst.refused {
                Some(limit) => format!(", refused at {}", limit),
                None => String::new(),
            }
        );
    }

    let sites = attribution::<N>(
        &statistics,
        probe.worst(),
        probe.monomial_bytes,
        pair_bytes::<N>(),
        2 * size_of::<usize>(),
    );

    let widths = [42, 12, 62];
    println!("\n| {:<40} | {:>10} | {:<60} |", "site", "MB", "method");
    println!("{}", rule(&widths));
    for site in &sites {
        println!(
            "| {:<40} | {:>10} | {:<60} |",
            site.name,
            mb(site.bytes),
            site.method
        );
    }

    // The residual: what the allocator saw during the run and the stage peaks above do not name.
    // Printed rather than distributed, because a number attributed by subtraction is not a
    // measurement of anything.
    let named = probe
        .worst()
        .map(|w| w.symbolic_peak + w.construction_peak)
        .unwrap_or(0)
        .max(statistics.max_estimated_bytes);
    println!(
        "{}\n| {:<40} | {:>10} | {:<60} |",
        rule(&widths),
        "unnamed remainder of the measured peak",
        mb(run_peak.saturating_sub(named)),
        "run peak less the largest named stage peak"
    );

    if statistics.max_estimated_bytes > 0 {
        println!(
            "\nThe entry budget accounts for {:.2}% of the measured peak live heap.",
            100.0 * statistics.max_estimated_bytes as f64 / run_peak.max(1) as f64
        );
    }
    println!(
        "Monomials enqueued across the run: {} ({} MB had none been popped); queue high-water {} monomials ({} MB).",
        statistics.monomials_enqueued,
        mb(statistics.monomials_enqueued * probe.monomial_bytes),
        statistics.max_pending_monomials,
        mb(statistics.max_pending_monomials * probe.monomial_bytes)
    );
}

/// `size_of::<ScheduledPair<N>>()`, which the pair module does not export.
///
/// Reconstructed from the type's fields rather than read, because `ScheduledPair` is private: a
/// `CriticalPair<N>` plus the schedule key the queue wraps it in. Stated here so the figure in the
/// table is checkable against the struct.
fn pair_bytes<const N: usize>() -> usize {
    size_of::<CriticalPair<N>>() + 2 * size_of::<usize>()
}

/// A registered MQ instance by its scoreboard name, if its file is on disk.
///
/// Maps `fukuoka-mq-III-n20-seed0` to the published `ToyExample-type3-n20-seed0`, as
/// `examples/scoreboard.rs` does. The files are not redistributable and are not in the repository.
fn read_mq(name: &str) -> Option<MqInstance> {
    let directory = std::env::var("ZEEBRA_MQ_DIR").unwrap_or("research/instances/mq".to_string());
    let file = name
        .strip_prefix("fukuoka-mq-")
        .map(|rest| {
            rest.replacen("III-", "type3-", 1)
                .replacen("VI-", "type6-", 1)
        })
        .map(|rest| format!("ToyExample-{}", rest))
        .unwrap_or_else(|| name.to_string());
    let text = std::fs::read_to_string(std::path::Path::new(&directory).join(file)).ok()?;
    MqInstance::parse(&text).ok()
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let entries: usize = std::env::var("ZEEBRA_MAX_ENTRIES")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(20_000_000);

    if arguments.first().map(String::as_str) == Some("mq") {
        let Some(name) = arguments.get(1) else {
            eprintln!("usage: f4_memory mq <instance>");
            return;
        };
        // The frontier budget `examples/scoreboard.rs` runs the ladder under: ten times the
        // columns, a byte cap set high enough that the entry count binds, and a batch cap.
        let options = F4Options {
            max_matrix_columns: 200_000,
            max_live_nonzeros: entries,
            max_live_bytes: 64_000_000_000,
            max_batches: Some(10_000),
            ..F4Options::default()
        };
        let Some(instance) = read_mq(name) else {
            eprintln!(
                "{} is not on disk under {}; run tools/fetch-mq-challenge.sh",
                name,
                std::env::var("ZEEBRA_MQ_DIR").unwrap_or("research/instances/mq".to_string())
            );
            return;
        };
        match instance.system::<20, Zp31>() {
            Ok(system) => report(
                name,
                &system,
                MonomialOrder::GradedReverseLexicographic,
                &options,
            ),
            Err(error) => eprintln!("{}: {} (this example compiles N = 20 only)", name, error),
        }
        return;
    }

    // The benchmark systems, which finish, so the attribution can be read on a run that is not
    // about a refusal. Small enough for a developer loop and for CI.
    let options = F4Options::default();
    let wanted = arguments.first().map(String::as_str);
    if wanted.is_none() || wanted == Some("katsura-6") {
        report(
            "katsura-6",
            &katsura::<6, Zp2147483647>(),
            MonomialOrder::GradedReverseLexicographic,
            &options,
        );
    }
    if wanted.is_none() || wanted == Some("katsura-7") {
        report(
            "katsura-7",
            &katsura::<7, Zp2147483647>(),
            MonomialOrder::GradedReverseLexicographic,
            &options,
        );
    }
    if wanted.is_none() || wanted == Some("cyclic-6") {
        report(
            "cyclic-6",
            &cyclic::<6, Zp2147483647>(),
            MonomialOrder::GradedReverseLexicographic,
            &options,
        );
    }
}
