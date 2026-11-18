//! #859: per-batch cost model of symbolic preprocessing on the shipping F4 path.
//!
//! Production F4 runs unchanged; before each batch the observer replays that batch's closure on the
//! live basis and pairs. `components` times the shipping closure (`PairMultiples::Distinct`) and
//! then each of its parts alone, over the same monomials in the same order, so the parts' sum
//! against the whole is checked rather than assumed. `level` prices #827's level-parallel
//! prototype against the serial closure it must equal (both seed every pair half, as the prototype
//! has no seed policy). Replays never feed back into F4, so the trajectory is the live one.
//!
//! cargo run --release --features external-runners,research-work --example symbolic_cost_model -- \
//!     --target eco12-wide64 --workers 16 --replay components|level [--level-workers 16]
//!     [--min-frontier 256]
use std::{
    alloc::{GlobalAlloc, Layout, System},
    collections::{HashSet, VecDeque},
    hash::BuildHasher,
    hint::black_box,
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
    time::{Duration, Instant},
};
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        differential::polynomial_to_string,
        external::corpus,
        f4::{
            f4_observed, f4_reported,
            symbolic::{
                symbolic_preprocessing_level_parallel_measured, symbolic_preprocessing_seeded,
                symbolic_preprocessing_with, BuildMonomialHasher, MonicBasis, MonomialHandle,
                MonomialSet, Preprocessed, ReducerCache, SymbolicCounts,
            },
            symbolic_intern::{
                symbolic_preprocessing_interned, with_live, InternConfig, InternReport, Merge,
                Retain,
            },
            BatchObserver,
        },
        pairs::CriticalPair,
        F4Options, PairMultiples, ParallelForward, ParallelSymbolic,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, Monomial, MonomialMap, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const TARGETS: &[&str] = &[
    "mq10-32003",
    "mq10-m31",
    "eco12-wide64",
    "mq11-goldilocks",
    "katsura11-m31",
    // #861: the small tasks the <=5% regression limit is read on.
    "katsura6-m31",
    "katsura7-m31",
    "cyclic6-m31",
    // #861: mid-size controls, between the small tasks and MQ10.
    "katsura8-m31",
    "cyclic7-m31",
];

/// Counts every allocation the process makes; the replay reads the difference across one call.
struct Counting;
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static ALLOCATED_BYTES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(layout.size(), Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Relaxed);
        ALLOCATED_BYTES.fetch_add(new_size, Relaxed);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Replay {
    Components,
    Level,
    /// #860: replay each batch serially and through an interning prototype.
    Intern,
    /// #860: no replay; live F4 with the prototype serving every batch (`--merge off`: shipping).
    Live,
}

#[derive(Debug, PartialEq)]
struct Args {
    target: String,
    workers: usize,
    replay: Replay,
    level_workers: usize,
    min_frontier: usize,
    merge: Option<Merge>,
    slices: usize,
    min_seed_rows: usize,
    retain: Retain,
    stages: bool,
    /// #861: `--merge auto`, the shipped `F4Options::parallel_symbolic` with `--level-workers`.
    auto: bool,
}

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        target: String::new(),
        workers: 0,
        replay: Replay::Components,
        level_workers: 16,
        min_frontier: 256,
        merge: Some(Merge::Serial),
        slices: 4,
        min_seed_rows: 0,
        retain: Retain::Batch,
        stages: false,
        auto: false,
    };
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        let positive = |v: String, what: &str| {
            v.parse()
                .ok()
                .filter(|&w: &usize| w > 0)
                .ok_or(format!("{what} takes a positive integer"))
        };
        match arg.as_str() {
            "--target" => parsed.target = value()?,
            "--workers" => parsed.workers = positive(value()?, "--workers")?,
            "--level-workers" => parsed.level_workers = positive(value()?, "--level-workers")?,
            "--min-frontier" => {
                parsed.min_frontier = value()?.parse().map_err(|_| "--min-frontier: integer")?
            }
            "--merge" => {
                let merge = value()?;
                parsed.auto = merge == "auto";
                parsed.merge = match merge.as_str() {
                    "off" | "auto" => None,
                    "serial" => Some(Merge::Serial),
                    "sharded" => Some(Merge::Sharded),
                    other => return Err(format!("unknown merge {other}")),
                }
            }
            "--slices" => parsed.slices = positive(value()?, "--slices")?,
            "--min-seed-rows" => {
                parsed.min_seed_rows = value()?.parse().map_err(|_| "--min-seed-rows: integer")?
            }
            "--retain" => {
                parsed.retain = match value()?.as_str() {
                    "batch" => Retain::Batch,
                    "run" => Retain::Run,
                    other => return Err(format!("unknown retain {other}")),
                }
            }
            "--stages" => parsed.stages = true,
            "--replay" => {
                parsed.replay = match value()?.as_str() {
                    "components" => Replay::Components,
                    "level" => Replay::Level,
                    "intern" => Replay::Intern,
                    "live" => Replay::Live,
                    other => return Err(format!("unknown replay {other}")),
                }
            }
            other => return Err(format!("unknown argument {other}")),
        }
    }
    if !TARGETS.contains(&parsed.target.as_str()) {
        return Err(format!("--target must be one of {TARGETS:?}"));
    }
    if parsed.workers == 0 {
        return Err("--workers is required".into());
    }
    if parsed.replay == Replay::Intern && parsed.merge.is_none() {
        return Err("--replay intern needs a merge".into());
    }
    Ok(parsed)
}

/// Shipping defaults; forward elimination serial at one worker and capped at `workers` above.
fn options(workers: usize) -> F4Options {
    F4Options {
        parallel_forward: if workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: workers,
            }
        },
        ..F4Options::default()
    }
}

struct Input {
    modulus: String,
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

fn ladder(problem: &str, modulus: u64) -> Input {
    let input = corpus::instance(problem, modulus, ORDER).expect("published ladder row");
    Input {
        modulus: modulus.to_string(),
        digest: input.digest(),
        variables: input.variables.clone(),
        generators: input.system.clone(),
    }
}

/// A frozen #738 row, refused unless its canonical text still hashes to its digest.
fn wide(field: &str, name: &str) -> Input {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/research/wide-corpus/cases.json"
    );
    let cases = Json::parse(&std::fs::read_to_string(path).expect("frozen wide catalog")).unwrap();
    let case = cases
        .items()
        .iter()
        .find(|c| {
            c.get("field").and_then(Json::as_str) == Some(field)
                && c.get("name").and_then(Json::as_str) == Some(name)
        })
        .expect("frozen wide row");
    let text = |key| case.get(key).and_then(Json::as_str).unwrap().to_string();
    let strings = |key| -> Vec<String> {
        case.get(key)
            .unwrap()
            .items()
            .iter()
            .map(|s| s.as_str().unwrap().to_string())
            .collect()
    };
    let digest = text("digest");
    assert_eq!(sha256_hex(text("canonical").as_bytes()), digest);
    Input {
        modulus: text("modulus"),
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    }
}

fn allocations() -> (usize, usize) {
    (ALLOCATIONS.load(Relaxed), ALLOCATED_BYTES.load(Relaxed))
}

/// Time `f`, returning its value, the wall, and the allocations it made.
fn timed<R>(f: impl FnOnce() -> R) -> (R, Duration, usize, usize) {
    let (count, bytes) = allocations();
    let started = Instant::now();
    let result = f();
    let elapsed = started.elapsed();
    let (count_after, bytes_after) = allocations();
    (result, elapsed, count_after - count, bytes_after - bytes)
}

/// Bytes a hashbrown table of `capacity` slots of `entry` bytes holds (buckets plus control bytes).
fn table_bytes(capacity: usize, entry: usize) -> usize {
    let buckets = if capacity == 0 {
        0
    } else {
        (capacity * 8 / 7).next_power_of_two()
    };
    buckets * (entry + 1)
}

struct Observer {
    replay: Replay,
    intern: Option<InternConfig>,
    options: F4Options,
    level_workers: usize,
    min_frontier: usize,
    batches: Vec<Json>,
    totals: [Duration; 2],
}

impl Observer {
    fn components<const N: usize, F: FiniteField>(
        &self,
        basis: &MonicBasis<N, F>,
        pairs: &[CriticalPair<N>],
    ) -> Json {
        let selection = self.options.reducer_selection;
        let shipping = || {
            symbolic_preprocessing_seeded(
                basis,
                pairs,
                usize::MAX,
                selection,
                &mut ReducerCache::new(self.options.reducer_cache),
                self.options.pair_multiples,
            )
            .expect("unbounded")
        };
        // Alternate the whole closure before and after its parts, so neither always runs cold.
        let first = self.batches.len().is_multiple_of(2);
        let early = first.then(|| timed(shipping));

        // Inputs the parts replay, prepared outside every clock.
        let reference = shipping();
        let lcms: MonomialSet<N> = pairs.iter().map(|p| p.lcm).collect();
        let lead: Vec<bool> = reference
            .monomials
            .iter()
            .map(|m| !lcms.contains(m) && reference.leading_monomials.contains(m))
            .collect();
        let queried: Vec<Monomial<N>> = reference
            .monomials
            .iter()
            .copied()
            .filter(|m| !lcms.contains(m))
            .collect();
        let shift_all = |each: &mut dyn FnMut(Monomial<N>)| {
            for row in &reference.rows {
                for (term, _) in basis.shifted_terms(row.basis_index, &row.multiplier) {
                    each(term);
                }
            }
        };

        let (_, seed, ..) = timed(|| {
            let mut keys: HashSet<(usize, Monomial<N>), BuildMonomialHasher> =
                HashSet::with_capacity_and_hasher(2 * pairs.len(), BuildMonomialHasher);
            let mut rows = Vec::with_capacity(2 * pairs.len());
            let mut covered = MonomialSet::<N>::default();
            for pair in pairs {
                for index in [pair.left, pair.right] {
                    let multiplier = pair
                        .lcm
                        .checked_div(&basis.element(index).leading_monomial)
                        .unwrap();
                    if self.options.pair_multiples == PairMultiples::Distinct
                        && !keys.insert((index, multiplier))
                    {
                        continue;
                    }
                    rows.push((index, multiplier));
                }
                covered.insert(pair.lcm);
            }
            black_box((rows, covered));
        });
        let (_, covered, ..) = timed(|| {
            let mut covered = lcms.clone();
            let mut hits = 0usize;
            for (monomial, &is_lead) in reference.monomials.iter().zip(&lead) {
                if covered.contains(monomial) {
                    hits += 1;
                    continue;
                }
                if is_lead {
                    covered.insert(*monomial);
                }
            }
            black_box((covered, hits));
        });
        let (counts, divisor, ..) = timed(|| {
            let mut counts = SymbolicCounts::default();
            for monomial in &queried {
                black_box(basis.find_divisor_with(monomial, selection, &mut counts));
            }
            counts
        });
        let (terms, shift, ..) = timed(|| {
            let mut terms = 0usize;
            shift_all(&mut |term| {
                black_box(term);
                terms += 1;
            });
            terms
        });
        let (_, shift_hash, ..) = timed(|| {
            shift_all(&mut |term| {
                black_box(BuildMonomialHasher.hash_one(term));
            })
        });
        let (interned, shift_intern, intern_allocs, intern_bytes) = timed(|| {
            let mut examined: MonomialMap<N, MonomialHandle> = MonomialMap::default();
            let mut arena: Vec<Monomial<N>> = Vec::new();
            let mut pending: VecDeque<Monomial<N>> = VecDeque::new();
            let mut handles: Vec<MonomialHandle> = Vec::new();
            shift_all(&mut |term| {
                let handle = *examined.entry(term).or_insert_with(|| {
                    arena.push(term);
                    pending.push_back(term);
                    (arena.len() - 1) as MonomialHandle
                });
                handles.push(handle);
            });
            (examined.capacity(), arena.len(), handles)
        });
        assert_eq!(interned.1, reference.monomials.len(), "intern replay");
        assert_eq!(interned.2, reference.term_handles, "intern replay order");
        let (_, queue, ..) = timed(|| {
            let mut pending: VecDeque<Monomial<N>> = VecDeque::new();
            for monomial in &reference.monomials {
                pending.push_back(*monomial);
            }
            while let Some(m) = pending.pop_front() {
                black_box(m);
            }
        });

        let late = (!first).then(|| timed(shipping));
        let (closure, full, allocs, alloc_bytes) = early.or(late).unwrap();
        assert_eq!(closure, reference, "the shipping closure is deterministic");
        assert_eq!(counts.divisor_queries, closure.counts.divisor_queries);
        assert_eq!(counts.divisor_scan_steps, closure.counts.divisor_scan_steps);
        let monomial = std::mem::size_of::<Monomial<N>>();
        let retained = |p: &Preprocessed<N>| {
            p.rows.capacity() * std::mem::size_of_val(&p.rows[0])
                + p.monomials.capacity() * monomial
                + p.term_handles.capacity() * std::mem::size_of::<MonomialHandle>()
                + table_bytes(p.leading_monomials.capacity(), monomial)
        };
        let parts = seed + covered + divisor + shift_intern;
        Json::object([
            ("pairs", Json::size(pairs.len())),
            ("basis", Json::size(basis.len())),
            ("rows", Json::size(closure.rows.len())),
            (
                "reducer_rows",
                Json::size(closure.rows.len() - lead_seed(&closure)),
            ),
            ("columns", Json::size(closure.monomials.len())),
            ("terms", Json::size(terms)),
            ("divisor_queries", Json::size(counts.divisor_queries)),
            ("divisor_scan_steps", Json::size(counts.divisor_scan_steps)),
            (
                "pair_multiples_removed",
                Json::size(closure.counts.pair_multiples_removed),
            ),
            (
                "max_pending",
                Json::size(closure.counts.max_pending_monomials),
            ),
            ("full_ns", Json::nanos(full)),
            ("seed_ns", Json::nanos(seed)),
            ("covered_ns", Json::nanos(covered)),
            ("divisor_ns", Json::nanos(divisor)),
            ("shift_ns", Json::nanos(shift)),
            ("hash_ns", Json::nanos(shift_hash.saturating_sub(shift))),
            (
                "probe_insert_ns",
                Json::nanos(shift_intern.saturating_sub(shift_hash)),
            ),
            ("queue_ns", Json::nanos(queue)),
            ("residual_ns", Json::nanos(full.saturating_sub(parts))),
            ("parts_ns", Json::nanos(parts)),
            ("allocations", Json::size(allocs)),
            ("allocated_bytes", Json::size(alloc_bytes)),
            ("intern_allocations", Json::size(intern_allocs)),
            ("intern_allocated_bytes", Json::size(intern_bytes)),
            (
                "examined_table_bytes",
                Json::size(table_bytes(interned.0, monomial + 4)),
            ),
            ("retained_bytes", Json::size(retained(&closure))),
            ("monomial_bytes", Json::size(monomial)),
        ])
    }

    fn intern<const N: usize, F: FiniteField + Sync>(
        &self,
        basis: &MonicBasis<N, F>,
        pairs: &[CriticalPair<N>],
    ) -> (Json, Duration, Duration) {
        let selection = self.options.reducer_selection;
        let multiples = self.options.pair_multiples;
        let config = self.intern.expect("intern replay has a config");
        let serial = || {
            timed(|| {
                symbolic_preprocessing_seeded(
                    basis,
                    pairs,
                    usize::MAX,
                    selection,
                    &mut ReducerCache::disabled(),
                    multiples,
                )
                .unwrap()
            })
        };
        let parallel = || {
            timed(|| {
                let (result, report) = symbolic_preprocessing_interned(
                    basis,
                    pairs,
                    usize::MAX,
                    selection,
                    multiples,
                    &config,
                );
                (result.unwrap(), report)
            })
        };
        let ((s, s_time, ..), ((p, report), p_time, p_allocs, p_bytes)) =
            if self.batches.len().is_multiple_of(2) {
                let s = serial();
                (s, parallel())
            } else {
                let p = parallel();
                (serial(), p)
            };
        assert_eq!(s, p, "batch {}: closures differ", self.batches.len());
        (
            Json::object([
                ("pairs", Json::size(pairs.len())),
                ("rows", Json::size(s.rows.len())),
                ("columns", Json::size(s.monomials.len())),
                ("terms", Json::size(s.term_handles.len())),
                ("serial_ns", Json::nanos(s_time)),
                ("parallel_ns", Json::nanos(p_time)),
                ("fallback", Json::Bool(report.serial_fallback)),
                ("steps", Json::size(report.steps)),
                ("dispatched_steps", Json::size(report.dispatched_steps)),
                ("candidates", Json::size(report.candidates)),
                ("owners", Json::size(report.owners)),
                (
                    "worst_shard_imbalance_milli",
                    Json::size(report.worst_shard_imbalance_milli),
                ),
                ("spawn_ns", Json::nanos(report.spawn)),
                ("seed_ns", Json::nanos(report.seed)),
                ("scan_ns", Json::nanos(report.scan)),
                ("merge_ns", Json::nanos(report.merge)),
                ("emit_ns", Json::nanos(report.emit)),
                ("stitch_ns", Json::nanos(report.stitch)),
                ("allocations", Json::size(p_allocs)),
                ("allocated_bytes", Json::size(p_bytes)),
            ]),
            s_time,
            p_time,
        )
    }

    fn level<const N: usize, F: FiniteField + Sync>(
        &self,
        basis: &MonicBasis<N, F>,
        pairs: &[CriticalPair<N>],
    ) -> (Json, Duration, Duration) {
        let selection = self.options.reducer_selection;
        let serial = || {
            timed(|| {
                symbolic_preprocessing_with(
                    basis,
                    pairs,
                    usize::MAX,
                    selection,
                    &mut ReducerCache::disabled(),
                )
                .unwrap()
            })
        };
        let parallel = || {
            timed(|| {
                symbolic_preprocessing_level_parallel_measured(
                    basis,
                    pairs,
                    selection,
                    self.level_workers,
                    self.min_frontier,
                )
            })
        };
        let ((s, s_time, ..), ((p, report), p_time, ..)) = if self.batches.len().is_multiple_of(2) {
            let s = serial();
            (s, parallel())
        } else {
            let p = parallel();
            (serial(), p)
        };
        assert_eq!(s, p, "batch {}: closures differ", self.batches.len());
        let json = Json::object([
            ("pairs", Json::size(pairs.len())),
            ("rows", Json::size(s.rows.len())),
            ("columns", Json::size(s.monomials.len())),
            ("terms", Json::size(s.term_handles.len())),
            ("serial_ns", Json::nanos(s_time)),
            ("parallel_ns", Json::nanos(p_time)),
            ("levels", Json::size(report.levels)),
            ("parallel_levels", Json::size(report.parallel_levels)),
            ("max_frontier", Json::size(report.max_frontier)),
            (
                "parallel_frontier_monomials",
                Json::size(report.parallel_frontier_monomials),
            ),
            ("seed_terms", Json::size(report.seed_terms)),
            ("terms_known", Json::size(report.terms_known)),
            ("terms_interned", Json::size(report.terms_interned)),
            ("terms_admitted", Json::size(report.terms_admitted)),
            ("seed_ns", Json::nanos(report.seed)),
            ("scan_ns", Json::nanos(report.scan)),
            ("parallel_scan_ns", Json::nanos(report.parallel_scan)),
            ("slowest_slice_ns", Json::nanos(report.slowest_slice)),
            ("slice_busy_ns", Json::nanos(report.slice_busy)),
            ("commit_ns", Json::nanos(report.commit)),
        ]);
        (json, s_time, p_time)
    }
}

/// Pair-component rows lead the row list; everything after them is a reducer.
fn lead_seed<const N: usize>(p: &Preprocessed<N>) -> usize {
    p.rows
        .iter()
        .take_while(|r| !matches!(r.kind, zeebra::grobner::f4::symbolic::RowKind::Reducer))
        .count()
}

impl<const N: usize, F: FiniteField + Sync> BatchObserver<N, F> for Observer {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        let json = match self.replay {
            Replay::Components => {
                let json = self.components(basis, pairs);
                self.totals[0] += Duration::from_nanos(
                    json.get("full_ns").and_then(Json::as_int).unwrap() as u64,
                );
                json
            }
            Replay::Level => {
                let (json, s, p) = self.level(basis, pairs);
                self.totals[0] += s;
                self.totals[1] += p;
                json
            }
            Replay::Intern => {
                let (json, s, p) = self.intern(basis, pairs);
                self.totals[0] += s;
                self.totals[1] += p;
                json
            }
            Replay::Live => unreachable!("live runs observe nothing"),
        };
        self.batches.push(json);
    }
}

fn run<const N: usize, F: FiniteField + Sync>(input: Input, args: &Args) -> Json {
    assert_eq!(input.variables.len(), N, "variable count");
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
    let options = F4Options {
        measure_stages: args.stages,
        parallel_symbolic: if args.auto {
            ParallelSymbolic::Auto {
                max_workers: args.level_workers,
            }
        } else {
            ParallelSymbolic::Serial
        },
        ..options(args.workers)
    };
    let intern = args.merge.map(|merge| InternConfig {
        workers: args.level_workers,
        merge,
        min_frontier: args.min_frontier,
        slices_per_worker: args.slices,
        min_seed_rows: args.min_seed_rows,
        retain: args.retain,
    });
    if args.replay == Replay::Live {
        return live(&system, &options, intern, &input, args);
    }
    let mut observer = Observer {
        replay: args.replay,
        intern,
        options: options.clone(),
        level_workers: args.level_workers,
        min_frontier: args.min_frontier,
        batches: Vec::new(),
        totals: [Duration::ZERO; 2],
    };
    let started = Instant::now();
    let (basis, _) = f4_observed(&system, ORDER, &options, &mut observer).expect("F4");
    let elapsed = started.elapsed();
    Json::object([
        ("target", Json::string(&args.target)),
        ("modulus", Json::string(&input.modulus)),
        ("digest", Json::string(&input.digest)),
        ("workers", Json::size(args.workers)),
        (
            "replay",
            Json::string(format!("{:?}", args.replay).to_lowercase()),
        ),
        ("level_workers", Json::size(args.level_workers)),
        ("min_frontier", Json::size(args.min_frontier)),
        ("options", Json::string(format!("{options:?}"))),
        ("basis_elements", Json::size(basis.len())),
        ("observed_call_ns", Json::nanos(elapsed)),
        ("replay_serial_ns", Json::nanos(observer.totals[0])),
        ("replay_parallel_ns", Json::nanos(observer.totals[1])),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
        ("batches", Json::Array(observer.batches)),
    ])
}

/// One live F4 call with the prototype serving every batch (or the shipping path), for walls.
fn live<const N: usize, F: FiniteField + Sync>(
    system: &[MultivariatePolynomial<N, F>],
    options: &F4Options,
    intern: Option<InternConfig>,
    input: &Input,
    args: &Args,
) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let solve = || f4_reported(system, ORDER, options);
    let started = Instant::now();
    let ((result, stats), report) = match intern {
        Some(config) => with_live(config, solve),
        None => (solve(), InternReport::default()),
    };
    let elapsed = started.elapsed();
    let basis = result.expect("F4");
    let mut text: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, &names, ORDER))
        .collect();
    text.sort();
    let time = |d: Duration| {
        if args.stages {
            Json::nanos(d)
        } else {
            Json::Null
        }
    };
    Json::object([
        ("target", Json::string(&args.target)),
        ("modulus", Json::string(&input.modulus)),
        ("digest", Json::string(&input.digest)),
        ("workers", Json::size(args.workers)),
        ("replay", Json::string("live")),
        (
            "merge",
            Json::string(
                args.merge
                    .map_or(if args.auto { "auto" } else { "off" }.into(), |m| {
                        format!("{m:?}").to_lowercase()
                    }),
            ),
        ),
        ("level_workers", Json::size(args.level_workers)),
        ("min_frontier", Json::size(args.min_frontier)),
        ("slices", Json::size(args.slices)),
        ("min_seed_rows", Json::size(args.min_seed_rows)),
        (
            "retain",
            Json::string(format!("{:?}", args.retain).to_lowercase()),
        ),
        ("status", Json::string("complete")),
        ("f4_call_ns", Json::nanos(elapsed)),
        ("total_ns", time(stats.total)),
        ("symbolic_ns", time(stats.stages.symbolic)),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
        ("basis_elements", Json::size(basis.len())),
        (
            "basis_sha256",
            Json::string(sha256_hex(text.join("\n").as_bytes())),
        ),
        ("monomials_enqueued", Json::size(stats.monomials_enqueued)),
        ("divisor_queries", Json::size(stats.divisor_queries)),
        ("served_steps", Json::size(report.steps)),
        ("dispatched_steps", Json::size(report.dispatched_steps)),
        ("fallback", Json::Bool(report.serial_fallback)),
        ("scratch_growths", Json::size(report.growths)),
        ("scratch_rescans", Json::size(report.rescans)),
        ("scratch_bytes", Json::size(report.scratch_bytes)),
    ])
}

fn main() {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let report = match args.target.as_str() {
        "mq10-32003" => run::<10, Zp32003>(ladder("mq-random-10", 32003), &args),
        "mq10-m31" => run::<10, Zp2147483647>(ladder("mq-random-10", 2147483647), &args),
        "eco12-wide64" => run::<12, Wide>(wide("wide64", "eco-12"), &args),
        "mq11-goldilocks" => run::<11, Goldilocks>(wide("goldilocks", "mq-random-11"), &args),
        "katsura11-m31" => run::<11, Zp2147483647>(ladder("katsura-11", 2147483647), &args),
        "katsura6-m31" => run::<6, Zp2147483647>(ladder("katsura-6", 2147483647), &args),
        "katsura7-m31" => run::<7, Zp2147483647>(ladder("katsura-7", 2147483647), &args),
        "cyclic6-m31" => run::<6, Zp2147483647>(ladder("cyclic-6", 2147483647), &args),
        "katsura8-m31" => run::<8, Zp2147483647>(ladder("katsura-8", 2147483647), &args),
        "cyclic7-m31" => run::<7, Zp2147483647>(ladder("cyclic-7", 2147483647), &args),
        _ => unreachable!("validated"),
    };
    println!("{}", report.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Result<Args, String> {
        parse_args(&list.iter().map(|s| s.to_string()).collect::<Vec<_>>())
    }

    /// Defaults are the component replay at the #827 dispatch threshold; bad input is refused.
    #[test]
    fn arguments_are_validated() {
        let parsed = args(&["--target", "katsura11-m31", "--workers", "4"]).unwrap();
        assert_eq!(parsed.replay, Replay::Components);
        assert_eq!((parsed.level_workers, parsed.min_frontier), (16, 256));
        let level = args(&[
            "--target",
            "eco12-wide64",
            "--workers",
            "16",
            "--replay",
            "level",
            "--level-workers",
            "8",
        ])
        .unwrap();
        assert_eq!((level.replay, level.level_workers), (Replay::Level, 8));
        assert!(args(&["--target", "katsura-11", "--workers", "1"]).is_err());
        assert!(args(&["--target", "mq10-m31"]).is_err());
        assert!(args(&["--target", "mq10-m31", "--workers", "1", "--replay", "x"]).is_err());
    }

    /// #860 arms: the live control is `--merge off`, and an intern replay needs a merge.
    #[test]
    fn intern_and_live_arms_parse() {
        let base = ["--target", "mq10-m31", "--workers", "16"];
        let with = |extra: &[&str]| args(&[&base[..], extra].concat());
        let live = with(&["--replay", "live", "--merge", "off", "--stages"]).unwrap();
        assert_eq!(
            (live.replay, live.merge, live.stages),
            (Replay::Live, None, true)
        );
        let sharded = with(&["--replay", "intern", "--merge", "sharded", "--slices", "8"]).unwrap();
        assert_eq!((sharded.merge, sharded.slices), (Some(Merge::Sharded), 8));
        assert!(with(&["--replay", "intern", "--merge", "off"]).is_err());
        let auto = with(&["--replay", "live", "--merge", "auto"]).unwrap();
        assert_eq!((auto.merge, auto.auto), (None, true));
        assert!(with(&["--merge", "parallel"]).is_err());
    }

    /// A table's byte estimate rounds its slots up to a power of two with one control byte each.
    #[test]
    fn table_bytes_counts_buckets_and_control_bytes() {
        assert_eq!(table_bytes(0, 8), 0);
        assert_eq!(table_bytes(7, 8), 8 * 9);
        assert_eq!(table_bytes(14, 4), 16 * 5);
    }
}
