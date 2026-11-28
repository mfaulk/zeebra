//! #974 M33-Q: one fresh-process solve for the correctness, regression and Gate D campaigns
//! (`research/m33-qualification/`), and the #1011 M34 portfolio arms (`research/m34-qualification/`).
//! The M33 campaigns build this file at their recorded harness commit (`git show <harness>:…`), which
//! used only public API that F0 (`31e334bd`) already had; the M34 engines need Z0.
//!
//! cargo run --release --example m33_qualify -- --field FIELD --name ROW [--order grevlex|grlex|lex]
//!     [--engine entry|f4|cap16|adaptive|fewest-fl|sig] [--workers N] [--wall-s S] [--repeat K]
//!     [--sample-threads] [--input-only] [--measure-stages]
//!
//! `entry` is `f4_signature_reported` (the dispatch), `f4` the shipping default. The #1011 arms:
//! `cap16` is `f4` with `max_pairs_per_batch = Some(16)`, `adaptive` is `f4` under
//! `GradedEngine::Adaptive`, `fewest-fl` is `f4` with `ReducerSelection::FewestTerms` and
//! `BatchOrder::FaugereLachartre` (#997), and `sig` is the forced signature engine
//! (`sig_f4_reported`, `--features research-sigf4` only). A typed refusal or
//! budget stop is a normal exit with `status` "refused" or "stopped" and the error's `Debug` text.
//! `basis_m33` normalizes each element by its grevlex leading coefficient, as `basis_digest.py`
//! does, so graded-lex and lex bases digest like any reference's text; on a grevlex basis it equals
//! `examples/support/basis_digest.rs`.

use rand::{rngs::StdRng, SeedableRng};
use std::time::{Duration, Instant};
use zeebra::{
    fields::{
        BabyBear, KoalaBear, PrimeFieldElement64, Zp18446744073709551557, Zp2, Zp2147483647,
        Zp32003,
    },
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon, reimer},
        differential::polynomial_to_string,
        external::{corpus, FieldSpec, Instance},
        f4_reported, f4_signature_reported, BatchOrder, F4Options, GradedEngine, ParallelForward,
        ParallelSymbolic, ReducerSelection,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const CANONICAL: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const FIELDS: [(&str, u64); 8] = [
    ("gf2", 2),
    ("gf32003", 32003),
    ("m31", 2147483647),
    ("babybear", 2013265921),
    ("koalabear", 2130706433),
    ("w59", 18446744073709551557),
    ("wide64", 18446744073709551263),
    ("goldilocks", 18446744069414584321),
];

#[derive(Debug)]
struct Args {
    field: String,
    modulus: u64,
    name: String,
    order: MonomialOrder,
    engine: String,
    workers: usize,
    wall: Duration,
    repeat: usize,
    sample_threads: bool,
    /// Sets `F4Options::measure_stages`; only the #974 thread diagnosis uses it.
    measure_stages: bool,
    input_only: bool,
    catalog: bool,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut a = Args {
        field: String::new(),
        modulus: 0,
        name: String::new(),
        order: CANONICAL,
        engine: "entry".into(),
        workers: 1,
        wall: Duration::from_secs(180),
        repeat: 1,
        sample_threads: false,
        measure_stages: false,
        input_only: false,
        catalog: false,
    };
    let mut it = raw.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        let positive = |v: String| v.parse::<usize>().ok().filter(|&k| k > 0);
        match arg.as_str() {
            "--field" => a.field = value()?,
            "--name" => a.name = value()?,
            "--engine" => a.engine = value()?,
            "--workers" => {
                a.workers = positive(value()?).ok_or("--workers takes a positive integer")?
            }
            "--repeat" => {
                a.repeat = positive(value()?).ok_or("--repeat takes a positive integer")?
            }
            "--wall-s" => a.wall = Duration::from_secs(value()?.parse().map_err(|_| "--wall-s")?),
            "--order" => {
                a.order = match value()?.as_str() {
                    "grevlex" => CANONICAL,
                    "grlex" => MonomialOrder::GradedLexicographic,
                    "lex" => MonomialOrder::Lexicographic,
                    _ => return Err("--order must be grevlex, grlex or lex".into()),
                }
            }
            "--sample-threads" => a.sample_threads = true,
            "--measure-stages" => a.measure_stages = true,
            "--input-only" => a.input_only = true,
            "--catalog" => a.catalog = true,
            // An empty argv slot is a manifest parameter left unset (`{catalog}`).
            "" => {}
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    a.modulus = FIELDS
        .iter()
        .find(|f| f.0 == a.field)
        .ok_or("--field must be gf2, gf32003, m31, babybear, koalabear, w59, wide64 or goldilocks")?
        .1;
    if !ENGINES.contains(&a.engine.as_str()) {
        return Err(format!("--engine must be one of {}", ENGINES.join(", ")));
    }
    if a.engine == "sig" && !cfg!(feature = "research-sigf4") {
        return Err("--engine sig needs --features research-sigf4".into());
    }
    Ok(a)
}

const ENGINES: [&str; 6] = ["entry", "f4", "cap16", "adaptive", "fewest-fl", "sig"];

/// The forced signature engine's options for a `workers`-worker arm, as the dispatch builds them for
/// its own team (`sigf4/dispatch.rs`, `signature_options`): the cascade runs on the team when it has
/// more than one worker, and every other budget keeps the engine's default.
#[cfg(feature = "research-sigf4")]
fn sig_options(args: &Args) -> zeebra::grobner::sigf4::SigF4Options {
    zeebra::grobner::sigf4::SigF4Options {
        max_wall_time: Some(args.wall),
        workers: args.workers,
        parallel_cascade: args.workers > 1,
        ..zeebra::grobner::sigf4::SigF4Options::default()
    }
}

struct Input {
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

/// The frozen #738 catalog, compiled in so the binary does not embed its build directory (#1021).
const WIDE_CATALOG: &str = include_str!("../research/wide-corpus/cases.json");

/// A frozen #738 row (`research/wide-corpus/cases.json`), the form the F0 baseline timed the
/// wide-field rows in; refused unless its canonical text still hashes to its digest.
fn catalog(field: &str, name: &str) -> Result<Input, String> {
    let cases = Json::parse(WIDE_CATALOG).map_err(|e| format!("{e:?}"))?;
    let case = cases
        .items()
        .iter()
        .find(|c| {
            c.get("field").and_then(Json::as_str) == Some(field)
                && c.get("name").and_then(Json::as_str) == Some(name)
        })
        .ok_or(format!("no frozen row {field}/{name}"))?;
    let text = |key| {
        case.get(key)
            .and_then(Json::as_str)
            .unwrap_or_default()
            .to_string()
    };
    let strings = |key| -> Vec<String> {
        let items = case.get(key).map_or(&[][..], Json::items);
        items
            .iter()
            .filter_map(|s| s.as_str().map(str::to_string))
            .collect()
    };
    let digest = text("digest");
    if sha256_hex(text("canonical").as_bytes()) != digest {
        return Err(format!(
            "{field}/{name}: canonical text does not hash to its digest"
        ));
    }
    Ok(Input {
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    })
}

/// Dense MQ with every coefficient of degree ≤ 2 nonzero: `examples/wide_corpus.rs`'s
/// construction with its seed exposed, so `mq-full-N-s0` is the frozen `mq-random-N` row and any
/// other `S` is a fresh support (#1080's held-out rows). The seed is `0x73800000 + N + S·2³²`.
fn full_mq<const N: usize, F: FiniteField>(seed: u64) -> Vec<MultivariatePolynomial<N, F>> {
    let names: Vec<_> = (1..=N).map(|i| format!("x{i}")).collect();
    let refs: [&str; N] = std::array::from_fn(|i| names[i].as_str());
    let mut rng = StdRng::seed_from_u64(0x73800000 + N as u64 + (seed << 32));
    let mut coefficient = || loop {
        let c = F::random(&mut rng);
        if !c.is_zero() {
            break c;
        }
    };
    (0..N)
        .map(|_| {
            let mut terms = vec![coefficient().to_string()];
            for i in 0..N {
                terms.push(format!("{}*x{}", coefficient(), i + 1));
                for j in i..N {
                    terms.push(format!("{}*x{}*x{}", coefficient(), i + 1, j + 1));
                }
            }
            MultivariatePolynomial::parse(&terms.join("+"), refs).expect("dense polynomial")
        })
        .collect()
}

/// `katsura-N`, `eco-N`, `cyclic-N`, `noon-N`, `reimer-N`, `mq-random-N-sS` or `mq-full-N-sS` at `p`, in the
/// external contract's canonical form, exactly as `sig_f4_study --generate` builds the M33 rows.
fn generated(name: &str, p: u64) -> Result<Input, String> {
    fn render<const N: usize, F: FiniteField>(
        name: &str,
        family: &str,
        system: &[MultivariatePolynomial<N, F>],
        p: u64,
    ) -> Instance {
        let names: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let text = system
            .iter()
            .map(|q| polynomial_to_string(q, &refs, CANONICAL))
            .collect();
        Instance::new(name, family, FieldSpec::prime(p), names, text, CANONICAL)
    }
    fn family<F: FiniteField>(name: &str, family: &str, n: usize, p: u64) -> Option<Instance> {
        macro_rules! sized {
            ($($k:literal)*) => {
                match (family, n) {
                    $(("katsura", $k) => Some(render(name, family, &katsura::<$k, F>(), p)),
                      ("eco", $k) => Some(render(name, family, &eco::<$k, F>(), p)),
                      ("cyclic", $k) => Some(render(name, family, &cyclic::<$k, F>(), p)),
                      ("noon", $k) => Some(render(name, family, &noon::<$k, F>(), p)),
                      ("reimer", $k) => Some(render(name, family, &reimer::<$k, F>(), p)),)*
                    _ => None,
                }
            };
        }
        sized!(4 5 6 7 8 9 10 11 12 13)
    }
    fn full<F: FiniteField>(name: &str, n: usize, seed: u64, p: u64) -> Option<Instance> {
        macro_rules! sized {
            ($($k:literal)*) => {
                match n {
                    $($k => Some(render(name, "mq-full", &full_mq::<$k, F>(seed), p)),)*
                    _ => None,
                }
            };
        }
        sized!(4 5 6 7 8 9 10 11 12 13 14 15 16)
    }
    let refused = || format!("no generator for {name}");
    let (stem, seed) = match name.rsplit_once("-s") {
        Some((stem, seed)) if stem.starts_with("mq-random-") || stem.starts_with("mq-full-") => {
            (stem, Some(seed.parse::<u64>().map_err(|_| refused())?))
        }
        _ => (name, None),
    };
    let (fam, n) = stem.rsplit_once('-').ok_or_else(refused)?;
    let n: usize = n.parse().map_err(|_| refused())?;
    let instance = match (fam, seed) {
        ("mq-random", Some(seed)) => corpus::random_mq_instance(n, seed, p, CANONICAL),
        ("mq-full", Some(seed)) => match p {
            2147483647 => full::<Zp2147483647>(name, n, seed, p),
            2013265921 => full::<BabyBear>(name, n, seed, p),
            2130706433 => full::<KoalaBear>(name, n, seed, p),
            18446744073709551557 => full::<Zp18446744073709551557>(name, n, seed, p),
            18446744073709551263 => full::<Wide>(name, n, seed, p),
            18446744069414584321 => full::<Goldilocks>(name, n, seed, p),
            _ => None,
        }
        .ok_or_else(refused)?,
        (_, None) => match p {
            2 => family::<Zp2>(name, fam, n, p),
            32003 => family::<Zp32003>(name, fam, n, p),
            2147483647 => family::<Zp2147483647>(name, fam, n, p),
            2013265921 => family::<BabyBear>(name, fam, n, p),
            2130706433 => family::<KoalaBear>(name, fam, n, p),
            18446744073709551557 => family::<Zp18446744073709551557>(name, fam, n, p),
            18446744073709551263 => family::<Wide>(name, fam, n, p),
            _ => family::<Goldilocks>(name, fam, n, p),
        }
        .ok_or_else(refused)?,
        _ => return Err(refused()),
    };
    Ok(Input {
        digest: instance.digest(),
        variables: instance.variables.clone(),
        generators: instance.system.clone(),
    })
}

/// `m33-basis-v1` over elements made monic at their grevlex leading term (`basis_digest.py`).
fn basis_m33<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    modulus: u64,
) -> String {
    let mut elements: Vec<Vec<u8>> = basis
        .iter()
        .filter(|p| !p.is_zero())
        .map(|p| {
            let mut terms: Vec<_> = p.terms().iter().collect();
            let lead = terms.iter().max_by(|a, b| CANONICAL.cmp(a.0, b.0)).unwrap();
            let scale = lead.1.inverse();
            terms.sort_unstable_by(|a, b| a.0.exponents().cmp(b.0.exponents()));
            let mut bytes = Vec::new();
            for (monomial, coefficient) in terms {
                for &e in monomial.exponents() {
                    let mut e = e;
                    while e >= 0x80 {
                        bytes.push((e as u8 & 0x7f) | 0x80);
                        e >>= 7;
                    }
                    bytes.push(e as u8);
                }
                bytes.extend(format!("{};", *coefficient * scale).bytes());
            }
            bytes
        })
        .collect();
    elements.sort_unstable();
    let mut data = format!("m33-basis-v1 {modulus} {N}\n").into_bytes();
    for element in &elements {
        data.extend_from_slice(&(element.len() as u32).to_le_bytes());
        data.extend_from_slice(element);
    }
    sha256_hex(&data)
}

/// The most threads alive at once besides the main thread and the sampler (`/proc/self/task`
/// every 50 µs, as `sig_f4_study --sample-threads`); a lower bound.
/// Worker threads grouped into teams, the way `research/m33-qualification/thread-diag` groups them:
/// a team is the threads born before any of them is gone, so a birth after a member's disappearance
/// starts the next team. A team's exiting threads can briefly outlive its join (#1002); counting per
/// team keeps them out of the next team's figure.
#[derive(Default)]
struct Teams {
    team_of: std::collections::HashMap<u32, usize>,
    current: Vec<u32>,
    shrunk: bool,
    count: usize,
}

impl Teams {
    /// One sweep of `(tid, state)` for every worker thread: (running in total, running in the
    /// busiest team).
    fn observe(&mut self, sweep: &[(u32, char)]) -> (usize, usize) {
        let seen: std::collections::HashSet<u32> = sweep.iter().map(|&(t, _)| t).collect();
        self.shrunk |= self.current.iter().any(|t| !seen.contains(t));
        for &(tid, _) in sweep {
            if !self.team_of.contains_key(&tid) {
                if self.count == 0 || self.shrunk {
                    self.count += 1;
                    self.current.clear();
                    self.shrunk = false;
                }
                self.team_of.insert(tid, self.count);
                self.current.push(tid);
            }
        }
        let mut per_team = std::collections::HashMap::new();
        let mut total = 0;
        for &(tid, _) in sweep.iter().filter(|&&(_, s)| s == 'R') {
            total += 1;
            *per_team.entry(self.team_of[&tid]).or_insert(0usize) += 1;
        }
        (total, per_team.values().copied().max().unwrap_or(0))
    }
}

/// Thread peaks over a call: listed worker threads (`/proc/self/task` entries less the caller and
/// the sampler), worker threads in state R, and the most in state R within one team.
#[derive(Clone, Copy, Default)]
struct ThreadPeaks {
    listed: usize,
    running: usize,
    team_running: usize,
}

fn worker_states(main: u32, own: u32) -> Vec<(u32, char)> {
    let Ok(dir) = std::fs::read_dir("/proc/self/task") else {
        return Vec::new();
    };
    dir.flatten()
        .filter_map(|e| {
            let tid = e.file_name().to_str()?.parse::<u32>().ok()?;
            if tid == main || tid == own {
                return None;
            }
            let stat = std::fs::read_to_string(e.path().join("stat")).ok()?;
            Some((tid, stat.rsplit_once(") ")?.1.chars().next()?))
        })
        .collect()
}

fn sampled<T>(on: bool, body: impl FnOnce() -> T) -> (T, Option<ThreadPeaks>) {
    use std::sync::{atomic::AtomicBool, atomic::Ordering::Relaxed, Arc};
    if !on {
        return (body(), None);
    }
    let stop = Arc::new(AtomicBool::new(false));
    let flag = stop.clone();
    let main = std::process::id();
    let sampler = std::thread::spawn(move || {
        let own = std::fs::read_link("/proc/thread-self")
            .ok()
            .and_then(|p| p.file_name()?.to_str()?.parse::<u32>().ok())
            .unwrap_or(0);
        let (mut peaks, mut teams) = (ThreadPeaks::default(), Teams::default());
        while !flag.load(Relaxed) {
            let sweep = worker_states(main, own);
            let (running, team_running) = teams.observe(&sweep);
            peaks.listed = peaks.listed.max(sweep.len());
            peaks.running = peaks.running.max(running);
            peaks.team_running = peaks.team_running.max(team_running);
            std::thread::sleep(Duration::from_micros(50));
        }
        peaks
    });
    let out = body();
    stop.store(true, Relaxed);
    (out, Some(sampler.join().expect("sampler")))
}

fn options(args: &Args) -> F4Options {
    let shared = shared_options(args);
    match args.engine.as_str() {
        "cap16" => F4Options {
            max_pairs_per_batch: Some(16),
            ..shared
        },
        "adaptive" => F4Options {
            graded_engine: GradedEngine::Adaptive,
            ..shared
        },
        "fewest-fl" => F4Options {
            reducer_selection: ReducerSelection::FewestTerms,
            batch_order: BatchOrder::FaugereLachartre,
            ..shared
        },
        _ => shared,
    }
}

/// The options every engine starts from: the wall budget and `workers` as both teams' cap.
fn shared_options(args: &Args) -> F4Options {
    let w = args.workers;
    F4Options {
        max_wall_time: Some(args.wall),
        parallel_forward: if w == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto { max_workers: w }
        },
        parallel_symbolic: if w == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto { max_workers: w }
        },
        measure_stages: args.measure_stages,
        ..F4Options::default()
    }
}

fn run<const N: usize, F: FiniteField>(input: &Input, args: &Args) -> Vec<(&'static str, Json)> {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|g| MultivariatePolynomial::parse(g, names).expect("canonical generator"))
        .collect();
    let options = options(args);
    let mut calls = Vec::new();
    let mut last = None;
    let ((), threads) = sampled(args.sample_threads, || {
        for _ in 0..args.repeat {
            let clock = Instant::now();
            last = Some(match args.engine.as_str() {
                "entry" => {
                    let (result, report) = f4_signature_reported(&system, args.order, &options);
                    let route = format!("{:?}", report.route);
                    (
                        result.map_err(|e| format!("{e:?}")),
                        Some((route, report.workers)),
                    )
                }
                #[cfg(feature = "research-sigf4")]
                "sig" => {
                    let (result, _) = zeebra::grobner::sigf4::sig_f4_reported(
                        &system,
                        args.order,
                        &sig_options(args),
                    );
                    (
                        result.map_err(|e| format!("{e:?}")),
                        Some(("Forced".to_string(), args.workers)),
                    )
                }
                _ => {
                    let (result, statistics) = f4_reported(&system, args.order, &options);
                    // Only `adaptive` on a graded order records a dispatch decision.
                    let route = statistics
                        .graded_route
                        .map(|d| (format!("{:?}", d.route), d.workers));
                    (result.map_err(|e| format!("{e:?}")), route)
                }
            });
            calls.push(clock.elapsed());
        }
    });
    let (result, route) = last.expect("at least one call");
    let status = match &result {
        Ok(_) => "complete",
        Err(e) if e.contains("Unsupported") => "refused",
        Err(_) => "stopped",
    };
    vec![
        ("status", Json::string(status)),
        (
            "error",
            result.as_ref().err().map_or(Json::Null, Json::string),
        ),
        (
            "route",
            route.as_ref().map_or(Json::Null, |r| Json::string(&r.0)),
        ),
        (
            "team",
            route.as_ref().map_or(Json::Null, |r| Json::size(r.1)),
        ),
        (
            "basis_m33",
            result
                .as_ref()
                .map_or(Json::Null, |b| Json::string(basis_m33(b, args.modulus))),
        ),
        (
            "basis_elements",
            result.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        ("call_ns", Json::nanos(*calls.last().unwrap())),
        (
            "calls_ns",
            Json::Array(calls.iter().map(|&d| Json::nanos(d)).collect()),
        ),
        (
            "threads_peak",
            threads.map_or(Json::Null, |t| Json::size(t.listed)),
        ),
        (
            "running_peak",
            threads.map_or(Json::Null, |t| Json::size(t.running)),
        ),
        (
            "team_running_peak",
            threads.map_or(Json::Null, |t| Json::size(t.team_running)),
        ),
    ]
}

fn main() {
    let started = Instant::now();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let input = if args.catalog {
        catalog(&args.field, &args.name)
    } else {
        generated(&args.name, args.modulus)
    }
    .unwrap_or_else(|e| panic!("{e}"));
    let strings = |v: &[String]| Json::Array(v.iter().map(Json::string).collect());
    let mut fields = vec![
        ("field", Json::string(&args.field)),
        ("name", Json::string(&args.name)),
        ("modulus", Json::string(args.modulus.to_string())),
        ("digest", Json::string(&input.digest)),
    ];
    if args.input_only {
        fields.push(("variables", strings(&input.variables)));
        fields.push(("generators", strings(&input.generators)));
    } else {
        fields.push(("order", Json::string(args.order.name())));
        fields.push(("engine", Json::string(&args.engine)));
        fields.push(("workers", Json::size(args.workers)));
        macro_rules! dispatch {
            ($($p:literal => $f:ty),*) => {
                match (args.modulus, input.variables.len()) {
                    $(($p, 4) => run::<4, $f>(&input, &args), ($p, 5) => run::<5, $f>(&input, &args), ($p, 6) => run::<6, $f>(&input, &args),
                      ($p, 7) => run::<7, $f>(&input, &args), ($p, 8) => run::<8, $f>(&input, &args),
                      ($p, 9) => run::<9, $f>(&input, &args), ($p, 10) => run::<10, $f>(&input, &args),
                      ($p, 11) => run::<11, $f>(&input, &args), ($p, 12) => run::<12, $f>(&input, &args),)*
                    (p, n) => panic!("no instantiation for p = {p} with {n} variables"),
                }
            };
        }
        fields.extend(dispatch!(
            2 => Zp2, 32003 => Zp32003, 2147483647 => Zp2147483647,
            2013265921 => BabyBear, 2130706433 => KoalaBear,
            18446744073709551557 => Zp18446744073709551557, 18446744073709551263 => Wide,
            18446744069414584321 => Goldilocks
        ));
        fields.push((
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ));
        fields.push(("main_ns", Json::nanos(started.elapsed())));
    }
    println!("{}", Json::object(fields).to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// On a monic grevlex basis the digest equals `basis_digest.rs`'s pinned value, and scaling an
    /// element (as a graded-lex or lex basis may be scaled relative to grevlex) does not change it.
    #[test]
    fn digest_matches_the_pinned_value_and_ignores_scaling() {
        let parse = |s: &[&str]| -> Vec<MultivariatePolynomial<2, Zp32003>> {
            s.iter()
                .map(|t| MultivariatePolynomial::parse(t, ["x1", "x2"]).unwrap())
                .collect()
        };
        let pinned = "8fb196a0f7de4f7d36d2d8c6b34fb80eebd5f04658fcc799e1f2583781e5fefc";
        assert_eq!(
            basis_m33(&parse(&["x2^2+32002", "x1*x2+2", "x1^2+3*x2"]), 32003),
            pinned
        );
        assert_eq!(
            basis_m33(&parse(&["2*x2^2+32001", "x1*x2+2", "x1^2+3*x2"]), 32003),
            pinned
        );
    }

    /// #1200: BabyBear and KoalaBear are accepted, and their generated rows carry residues of their
    /// own prime (Katsura's `-1` as `p - 1`), not of the Goldilocks fallback.
    #[test]
    fn thirty_one_bit_ao_primes_generate_in_their_own_field() {
        for (field, p) in [("babybear", 2013265921u64), ("koalabear", 2130706433)] {
            let raw: Vec<String> = ["--field", field, "--name", "katsura-4"]
                .iter()
                .map(|s| s.to_string())
                .collect();
            assert_eq!(parse_args(&raw).unwrap().modulus, p);
            let input = generated("katsura-4", p).unwrap();
            let numbers: Vec<u64> = input
                .generators
                .iter()
                .flat_map(|g| g.split(|c: char| !c.is_ascii_digit() && c != 'x'))
                .filter(|t| !t.is_empty() && !t.starts_with('x'))
                .map(|t| t.parse().unwrap())
                .collect();
            assert!(numbers.iter().all(|&c| c < p), "{field}: {numbers:?}");
            assert!(
                numbers.contains(&(p - 1)),
                "{field}: no p - 1 in {numbers:?}"
            );
        }
    }

    /// #1080: `mq-full-N-s0` is the frozen wide-corpus dense row, polynomial for polynomial, and
    /// another seed is a different full-support system of the same shape.
    #[test]
    fn full_mq_seed_zero_is_the_frozen_wide_row() {
        let names: Vec<String> = (1..=10).map(|i| format!("x{i}")).collect();
        let refs: [&str; 10] = std::array::from_fn(|i| names[i].as_str());
        let parse = |input: &Input| -> Vec<MultivariatePolynomial<10, Goldilocks>> {
            input
                .generators
                .iter()
                .map(|g| MultivariatePolynomial::parse(g, refs).unwrap())
                .collect()
        };
        let p = 18446744069414584321;
        let frozen = catalog("goldilocks", "mq-random-10").unwrap();
        let zero = generated("mq-full-10-s0", p).unwrap();
        assert_eq!(parse(&zero), parse(&frozen));
        let fresh = generated("mq-full-10-s1", p).unwrap();
        assert_ne!(parse(&fresh), parse(&frozen));
        assert!(parse(&fresh).iter().all(|q| q.terms().len() == 1 + 10 + 55));
    }

    /// #1076: `reimer-N` renders the library's Reimer system, whose generators span degrees 2..=N+1.
    #[test]
    fn reimer_rows_are_generated() {
        let input = generated("reimer-5", 2147483647).unwrap();
        assert_eq!(input.generators.len(), 5);
        assert_eq!(input.variables.len(), 5);
        assert!(
            input.generators[4].contains("x1^6"),
            "{:?}",
            input.generators[4]
        );
    }

    /// Fields, orders and engines outside the suites are refused before any solve.
    #[test]
    fn arguments_are_validated() {
        let args = |l: &[&str]| parse_args(&l.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        assert!(args(&["--field", "w59", "--name", "katsura-4", "--order", "lex"]).is_ok());
        assert!(args(&["--field", "bn254", "--name", "katsura-4"]).is_err());
        assert!(args(&[
            "--field",
            "gf2",
            "--name",
            "katsura-4",
            "--order",
            "weighted"
        ])
        .is_err());
        assert!(args(&["--field", "gf2", "--name", "katsura-4", "--engine", "sigf4"]).is_err());
        let measured =
            args(&["--field", "gf2", "--name", "katsura-4", "--measure-stages"]).unwrap();
        assert!(measured.measure_stages && options(&measured).measure_stages);
        assert!(
            !options(&args(&["--field", "gf2", "--name", "katsura-4"]).unwrap()).measure_stages
        );
    }

    /// Each #1011 engine changes exactly its own option over the shared wall and worker settings, and
    /// `sig` is accepted only in a `research-sigf4` build.
    #[test]
    fn m34_engines_set_only_their_own_options() {
        let args = |engine: &str| {
            let raw: Vec<String> = [
                "--field",
                "gf32003",
                "--name",
                "katsura-4",
                "--workers",
                "4",
                "--engine",
                engine,
            ]
            .iter()
            .map(|s| s.to_string())
            .collect();
            parse_args(&raw)
        };
        let base = options(&args("f4").unwrap());
        assert_eq!(base.max_pairs_per_batch, None);
        assert_eq!(base.graded_engine, GradedEngine::Conventional);
        assert_eq!(base.reducer_selection, ReducerSelection::FirstApplicable);
        assert_eq!(base.batch_order, BatchOrder::Forward);
        assert_eq!(
            base.parallel_forward,
            ParallelForward::Auto { max_workers: 4 }
        );
        assert_eq!(
            options(&args("cap16").unwrap()),
            F4Options {
                max_pairs_per_batch: Some(16),
                ..base.clone()
            }
        );
        assert_eq!(
            options(&args("adaptive").unwrap()),
            F4Options {
                graded_engine: GradedEngine::Adaptive,
                ..base.clone()
            }
        );
        assert_eq!(
            options(&args("fewest-fl").unwrap()),
            F4Options {
                reducer_selection: ReducerSelection::FewestTerms,
                batch_order: BatchOrder::FaugereLachartre,
                ..base.clone()
            }
        );
        assert_eq!(
            args("sig").is_ok(),
            cfg!(feature = "research-sigf4"),
            "sig needs research-sigf4"
        );
    }

    fn solve(engine: &str, order: &str, workers: usize) -> (String, String) {
        let raw: Vec<String> = [
            "--field",
            "gf32003",
            "--name",
            "katsura-4",
            "--order",
            order,
            "--engine",
            engine,
            "--workers",
            &workers.to_string(),
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let args = parse_args(&raw).unwrap();
        let input = generated(&args.name, args.modulus).unwrap();
        let out = run::<4, Zp32003>(&input, &args);
        let get = |key: &str| {
            out.iter()
                .find(|(k, _)| *k == key)
                .map(|(_, v)| v.to_json())
                .unwrap()
        };
        (get("status"), get("basis_m33"))
    }

    /// Every #1011 engine returns the shipping F4's digest on Katsura-4 at one and four workers
    /// under grevlex and lex, except the forced signature engine, which refuses lex.
    #[test]
    fn m34_engines_return_the_f4_digest() {
        for order in ["grevlex", "lex"] {
            let (status, reference) = solve("f4", order, 1);
            assert_eq!(status, "\"complete\"");
            let mut engines = vec!["cap16", "adaptive", "fewest-fl", "f4"];
            if cfg!(feature = "research-sigf4") {
                engines.push("sig");
            }
            for engine in engines {
                for workers in [1, 4] {
                    let (status, digest) = solve(engine, order, workers);
                    if engine == "sig" && order == "lex" {
                        assert_eq!(status, "\"refused\"", "{engine} {order} {workers}");
                    } else {
                        assert_eq!(digest, reference, "{engine} {order} {workers}");
                    }
                }
            }
        }
    }

    /// A thread of a team that has begun to exit, running beside a full new team, counts toward the
    /// process total but not toward any one team's peak; a team running past the cap counts in both.
    #[test]
    fn running_threads_are_counted_per_team() {
        let mut teams = Teams::default();
        let first: Vec<(u32, char)> = (1..=4).map(|t| (t, 'R')).collect();
        assert_eq!(teams.observe(&first), (4, 4));
        // Thread 4 is gone, so the next births form a second team; thread 3 still runs.
        let mut overlap = vec![(3, 'R')];
        overlap.extend((10..14).map(|t| (t, 'R')));
        assert_eq!(teams.observe(&overlap[..1]), (1, 1));
        assert_eq!(teams.observe(&overlap), (5, 4));
        // A sleeping thread is not running.
        assert_eq!(teams.observe(&[(10, 'S'), (11, 'R')]), (1, 1));
        let mut wide = Teams::default();
        let five: Vec<(u32, char)> = (1..=5).map(|t| (t, 'R')).collect();
        assert_eq!(wide.observe(&five), (5, 5));
    }
}
