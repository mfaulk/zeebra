//! One fresh-process run of the #857 signature engine or the shipping F4 on a frozen wide-corpus
//! row; process wall belongs to the caller (`research/m30-sigf4/run.py`).
//!
//! cargo run --release --features research-sigf4 --example sig_f4_study -- \
//!     --field wide64 --name eco-12 --engine sigf4|f4|entry [--workers 16] [--wall-s 600]
//!     [--certify] [--claim]
//!
//! `--engine entry` runs the supported opt-in entry point, `grobner::f4_signature` with its
//! pre-solve dispatch (#905), under the same options as the `f4` arm; it reports the route taken.
//! `--field gf32003|m31` takes MQ10 (`--name mq-random-10`) from the published ladder, as
//! `m29_cost_model` does. #939's held-out candidates outside both catalogs (`goldilocks/cyclic-6`,
//! `m31/eco-11`, `gf32003/mq-random-9`) are generated here and refused unless they reproduce their
//! pinned digest (`research/m32-baseline/README.md`).
//!
//! `--generate` builds the row from its generator at any of the four fields instead of a catalog:
//! `katsura-N`, `eco-N`, `cyclic-N`, `noon-N`, or `mq-random-N-sS` (the ladder's MQ generator at
//! seed S), each in the external contract's canonical form, as M33's candidate pool is digested
//! (`research/m33-baseline/admission.py`); `--input-only` prints the row's digest, variables and
//! generators and solves nothing.
//!
//! Every complete run reports `basis_m33`, the `m33-basis-v1` digest
//! (`tools/external/basis_digest.py`) every M33 solver is compared by. `--digest-only` skips the
//! text render, so the process renders nothing (plan §11.3); `--write-basis PATH` writes the rendered
//! basis, one element per line, for a verification run.
//!
//! `--stages` (f4) turns on stage measurement and reports the stage clocks, the concurrent passes'
//! worker time and products, and the work counters (#972); `--fl` (f4) runs the Faugère–Lachartre
//! batch order, whose forward clock `--stages` splits into the sweep and `D'` (#918); `--reducer
//! NAME` (f4) sets the symbolic reducer selection by its `ReducerSelection` variant name.
//!
//! `--claim` (sigf4) runs #904's parallel cascade, #902's prereduce + claim schedule, on
//! `--workers` threads instead of design 2's serial cascade pass.
//!
//! `--basis` prints the reduced basis's SHA-256 (sorted rendered text), which is how two engines'
//! outputs are compared coefficient for coefficient without holding both in one process. With
//! `--features research-work`, `--discovery` adds the shipping F4's serial census: forward and
//! backward coefficient products and those on rows that end zero (#835's instrument).
//!
//! With `--features research-sigf4-replay`, `--replay` (sigf4, `--workers ≥ 2`) runs design 1
//! twice, without and with recording, then design 2 recorded, and prints #902's cascade records
//! and schedule ceilings instead of a timing row; it refuses if recording moved any algebraic
//! quantity (`docs/research/m31-parallel-signature-elimination.md`).
//!
//! With `--features research-sigf4-replay`, `--symbolic-replay` (sigf4) replays every batch's
//! symbolic closure as #933's level-synchronous design at 1/4/8/16 workers beside the engine's own
//! (run at `--workers`, `--claim` as given), asserts each run equal to it, and prints the per-batch
//! clocks and the ceiling; `--min-frontier` (default 512) is the narrowest level a team scans
//! (`docs/research/m32-parallel-symbolic.md` §4).
#[path = "support/basis_digest.rs"]
mod basis_digest;

use std::time::{Duration, Instant};
use zeebra::{
    fields::{PrimeFieldElement64, Zp2147483647, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura, noon},
        certify_f4_output_with_workers,
        differential::polynomial_to_string,
        external::{corpus, ExternalSolver, FieldSpec, Instance, Limits, SingularSolver, Task},
        f4_reported, f4_signature_reported,
        reference::buchberger_reference,
        sigf4::{sig_f4_reported, SigF4Options, SigF4Statistics},
        BatchOrder, F4Options, F4Statistics, GradedEngine, ParallelForward, ParallelSymbolic,
        ReducerSelection,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
type Wide = PrimeFieldElement64<18446744073709551263>;
const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

#[derive(Debug, PartialEq)]
struct Args {
    field: String,
    name: String,
    engine: String,
    workers: usize,
    wall: Duration,
    certify: bool,
    discovery: bool,
    replay: bool,
    claim: bool,
    symbolic: bool,
    min_frontier: usize,
    repeat: usize,
    order: MonomialOrder,
    sample_threads: bool,
    generate: bool,
    input_only: bool,
    digest_only: bool,
    write_basis: Option<String>,
    stages: bool,
    fl: bool,
    reducer: ReducerSelection,
}

/// The engines that compute a basis independently of Zeebra's F4 and signature engines (#941).
const REFERENCES: [&str; 3] = ["groebner-rs", "singular", "reference"];

fn parse_args(args: &[String]) -> Result<Args, String> {
    let mut parsed = Args {
        field: String::new(),
        name: String::new(),
        engine: String::new(),
        workers: 1,
        wall: Duration::from_secs(600),
        certify: false,
        discovery: false,
        replay: false,
        claim: false,
        symbolic: false,
        min_frontier: 512,
        repeat: 1,
        order: ORDER,
        sample_threads: false,
        generate: false,
        input_only: false,
        digest_only: false,
        write_basis: None,
        stages: false,
        fl: false,
        reducer: ReducerSelection::default(),
    };
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || it.next().cloned().ok_or(format!("{arg} needs a value"));
        match arg.as_str() {
            "--field" => parsed.field = value()?,
            "--name" => parsed.name = value()?,
            "--engine" => parsed.engine = value()?,
            "--workers" => {
                parsed.workers = value()?
                    .parse()
                    .ok()
                    .filter(|&w| w > 0)
                    .ok_or("--workers takes a positive integer")?
            }
            "--wall-s" => {
                parsed.wall = Duration::from_secs(value()?.parse().map_err(|_| "--wall-s")?)
            }
            "--certify" => parsed.certify = true,
            "--sample-threads" => parsed.sample_threads = true,
            "--discovery" => parsed.discovery = true,
            "--generate" => parsed.generate = true,
            "--input-only" => parsed.input_only = true,
            "--digest-only" => parsed.digest_only = true,
            "--write-basis" => parsed.write_basis = Some(value()?),
            "--replay" => parsed.replay = true,
            "--claim" => parsed.claim = true,
            "--stages" => parsed.stages = true,
            "--fl" => parsed.fl = true,
            "--reducer" => {
                let name = value()?;
                parsed.reducer = ReducerSelection::ALL
                    .into_iter()
                    .find(|s| format!("{s:?}") == name)
                    .ok_or(format!("--reducer: no ReducerSelection::{name}"))?
            }
            "--symbolic-replay" => parsed.symbolic = true,
            "--min-frontier" => {
                parsed.min_frontier = value()?.parse().map_err(|_| "--min-frontier")?
            }
            "--repeat" => {
                parsed.repeat = value()?
                    .parse()
                    .ok()
                    .filter(|&k| k > 0)
                    .ok_or("--repeat takes a positive integer")?
            }
            "--order" => {
                parsed.order = match value()?.as_str() {
                    "grevlex" => MonomialOrder::GradedReverseLexicographic,
                    "grlex" => MonomialOrder::GradedLexicographic,
                    _ => return Err("--order must be grevlex or grlex".into()),
                }
            }
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    if !["goldilocks", "wide64", "gf32003", "m31"].contains(&parsed.field.as_str()) {
        return Err("--field must be goldilocks, wide64, gf32003 or m31".into());
    }
    if !["sigf4", "f4", "entry", "adaptive"].contains(&parsed.engine.as_str())
        && !REFERENCES.contains(&parsed.engine.as_str())
    {
        return Err(
            "--engine must be sigf4, f4, entry, adaptive, groebner-rs, singular or reference"
                .into(),
        );
    }
    if REFERENCES.contains(&parsed.engine.as_str()) && (parsed.repeat > 1 || parsed.certify) {
        return Err("a reference engine is neither timed repeatedly nor certified".into());
    }
    if parsed.discovery && (parsed.engine != "f4" || parsed.workers != 1) {
        return Err("--discovery observes the serial shipping F4 only".into());
    }
    if (parsed.stages || parsed.fl || parsed.reducer != ReducerSelection::default())
        && parsed.engine != "f4"
    {
        return Err("--stages and --fl configure the shipping F4: --engine f4".into());
    }
    if parsed.claim && (parsed.engine != "sigf4" || parsed.replay) {
        return Err("--claim runs the signature engine's parallel cascade: --engine sigf4".into());
    }
    if parsed.symbolic && (parsed.engine != "sigf4" || parsed.replay) {
        return Err(
            "--symbolic-replay replays the signature engine's closure: --engine sigf4".into(),
        );
    }
    if parsed.repeat > 1 && (parsed.certify || parsed.discovery || parsed.replay || parsed.symbolic)
    {
        return Err("--repeat times the solve alone".into());
    }
    if parsed.replay && (parsed.engine != "sigf4" || parsed.workers < 2) {
        return Err("--replay runs design 1 and design 2: --engine sigf4 --workers ≥ 2".into());
    }
    Ok(parsed)
}

/// Shipping defaults; only the forward and symbolic worker caps vary, as in `m29_cost_model`.
fn f4_options(args: &Args) -> F4Options {
    F4Options {
        max_wall_time: Some(args.wall),
        parallel_forward: if args.workers == 1 {
            ParallelForward::Serial
        } else {
            ParallelForward::Auto {
                max_workers: args.workers,
            }
        },
        parallel_symbolic: if args.workers == 1 {
            ParallelSymbolic::Serial
        } else {
            ParallelSymbolic::Auto {
                max_workers: args.workers,
            }
        },
        measure_stages: args.stages,
        reducer_selection: args.reducer,
        batch_order: if args.fl {
            BatchOrder::FaugereLachartre
        } else {
            BatchOrder::Forward
        },
        ..F4Options::default()
    }
}

/// #972: the shipping F4's stage clocks, concurrent-pass timings and work counters.
fn f4_stage_statistics(s: &F4Statistics) -> Json {
    let st = &s.stages;
    let p = &s.parallel_forward;
    let c = &s.candidate_reduction;
    Json::object([
        ("symbolic_ns", Json::nanos(st.symbolic)),
        ("construction_ns", Json::nanos(st.construction)),
        ("elimination_ns", Json::nanos(st.elimination)),
        ("forward_ns", Json::nanos(st.forward)),
        ("fl_sweep_ns", Json::nanos(st.fl_sweep)),
        ("fl_echelon_ns", Json::nanos(st.fl_echelon)),
        ("backward_ns", Json::nanos(st.backward)),
        ("extraction_ns", Json::nanos(st.extraction)),
        ("interreduction_ns", Json::nanos(st.interreduction)),
        ("total_ns", Json::nanos(s.total)),
        ("parallel_batches", Json::size(p.batches)),
        ("parallel_fallback_batches", Json::size(p.fallback_batches)),
        ("passes", Json::size(p.passes)),
        ("worker_slots", Json::size(p.worker_slots)),
        ("busy_ns", Json::int(p.busy_ns)),
        ("critical_ns", Json::int(p.critical_ns)),
        ("scheduling_ns", Json::int(p.scheduling_ns)),
        ("publication_ns", Json::int(p.publication_ns)),
        ("parallel_products", Json::size(p.products)),
        ("retry_products", Json::size(p.retry_products)),
        ("lost_publications", Json::size(p.lost_publications)),
        ("backward_products", Json::size(c.coefficient_products)),
        ("backward_targets", Json::size(c.targets)),
        ("backward_parallel_batches", Json::size(c.parallel_batches)),
        ("row_operations", Json::size(s.row_operations)),
        ("pivot_inversions", Json::size(s.pivot_inversions)),
        ("reducer_rows", Json::size(s.reducer_rows)),
        ("initial_nonzeros", Json::size(s.total_initial_nonzeros)),
        ("final_nonzeros", Json::size(s.total_final_nonzeros)),
        ("max_live_nonzeros", Json::size(s.max_live_nonzeros)),
    ])
}

struct Input {
    digest: String,
    variables: Vec<String>,
    generators: Vec<String>,
}

/// MQ10 at the two M29 primes, from the published ladder under its pinned digest.
fn ladder(field: &str, name: &str) -> Input {
    let modulus = if field == "gf32003" {
        32003
    } else {
        2147483647
    };
    let input = corpus::instance(name, modulus, ORDER).expect("published ladder entry");
    let entry = corpus::ladder().into_iter().find(|e| e.name == input.name);
    assert_eq!(
        entry.and_then(|e| e.digest_at(modulus).map(str::to_string)),
        Some(input.digest())
    );
    Input {
        digest: input.digest(),
        variables: input.variables.clone(),
        generators: input.system.clone(),
    }
}

/// #939's held-out candidates (plan §10.1) by canonical SHA-256: `wide64/mq-random-12` and
/// `goldilocks/mq-random-10` are frozen in the wide catalog, `m31/katsura-10` in the published
/// ladder; the rest are generated by [`held_out`].
const HELD_OUT: [(&str, &str, &str); 6] = [
    (
        "goldilocks",
        "mq-random-10",
        "f69e955f898956df18bf174d1635f4f2cef7cf3e457e101713e826b3674a7bf3",
    ),
    (
        "wide64",
        "mq-random-12",
        "549302dc73ca71fcacde392a0e24dc4c26f469159b880d29a6b01c62c0a300a6",
    ),
    (
        "gf32003",
        "mq-random-9",
        "4e4ddcb645c8f6eddb73d21a1532437643f7a2a2a6faf6643886d1c4a5076b21",
    ),
    (
        "m31",
        "katsura-10",
        "67d6a96fadd21cc7a295c7100c93d84d2d7be37d9b7927377e57f973ebbbc8b0",
    ),
    (
        "m31",
        "eco-11",
        "3bdb17005b060d861412758860684229498a54906f610b9854b6bd09d8d11951",
    ),
    (
        "goldilocks",
        "cyclic-6",
        "2867c8eb39e07bec37ecb907e5b6971146a479594b0a9fc5ba20b64650a0c918",
    ),
];

/// A held-out candidate in neither catalog, in the external contract's canonical form (as the
/// ladder's rows are), or `None` for any other row. The MQ seed is the ladder's rule, seed = n.
fn held_out(field: &str, name: &str) -> Option<Input> {
    fn render<const N: usize, F: FiniteField>(
        name: &str,
        family: &str,
        system: &[MultivariatePolynomial<N, F>],
        modulus: u64,
    ) -> Instance {
        let names: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let text = system
            .iter()
            .map(|p| polynomial_to_string(p, &refs, ORDER))
            .collect();
        Instance::new(name, family, FieldSpec::prime(modulus), names, text, ORDER)
    }
    let instance = match (field, name) {
        ("goldilocks", "cyclic-6") => render(
            name,
            "cyclic",
            &cyclic::<6, Goldilocks>(),
            18446744069414584321,
        ),
        ("m31", "eco-11") => render(name, "eco", &eco::<11, Zp2147483647>(), 2147483647),
        ("gf32003", "mq-random-9") => corpus::random_mq_instance(9, 9, 32003, ORDER),
        _ => return None,
    };
    let pinned = HELD_OUT
        .iter()
        .find(|(f, n, _)| (*f, *n) == (field, name))
        .map(|row| row.2);
    assert_eq!(Some(instance.digest().as_str()), pinned, "{field}/{name}");
    Some(Input {
        digest: instance.digest(),
        variables: instance.variables.clone(),
        generators: instance.system.clone(),
    })
}

/// The modulus of each `--field`.
fn modulus(field: &str) -> u64 {
    match field {
        "goldilocks" => 18446744069414584321,
        "wide64" => 18446744073709551263,
        "gf32003" => 32003,
        "m31" => 2147483647,
        _ => panic!("unknown field {field}"),
    }
}

/// `--generate`: the row built from its generator at `field`, in the external contract's form.
fn generated(field: &str, name: &str) -> Result<Input, String> {
    fn render<const N: usize, F: FiniteField>(
        name: &str,
        family: &str,
        system: &[MultivariatePolynomial<N, F>],
        modulus: u64,
    ) -> Instance {
        let names: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let text = system
            .iter()
            .map(|p| polynomial_to_string(p, &refs, ORDER))
            .collect();
        Instance::new(name, family, FieldSpec::prime(modulus), names, text, ORDER)
    }
    fn family<F: FiniteField>(name: &str, family: &str, n: usize, p: u64) -> Option<Instance> {
        macro_rules! sized {
            ($($k:literal)*) => {
                match (family, n) {
                    $(("katsura", $k) => Some(render(name, family, &katsura::<$k, F>(), p)),
                      ("eco", $k) => Some(render(name, family, &eco::<$k, F>(), p)),
                      ("cyclic", $k) => Some(render(name, family, &cyclic::<$k, F>(), p)),
                      ("noon", $k) => Some(render(name, family, &noon::<$k, F>(), p)),)*
                    _ => None,
                }
            };
        }
        sized!(4 5 6 7 8 9 10 11 12 13 14)
    }
    let p = modulus(field);
    let refused = || format!("--generate has no generator for {name}");
    let (stem, seed) = match name.rsplit_once("-s") {
        Some((stem, seed)) if stem.starts_with("mq-random-") => {
            (stem, Some(seed.parse::<u64>().map_err(|_| refused())?))
        }
        _ => (name, None),
    };
    let (fam, n) = stem.rsplit_once('-').ok_or_else(refused)?;
    let n: usize = n.parse().map_err(|_| refused())?;
    let instance = match (fam, seed) {
        ("mq-random", Some(seed)) => corpus::random_mq_instance(n, seed, p, ORDER),
        (_, None) => match field {
            "goldilocks" => family::<Goldilocks>(name, fam, n, p),
            "wide64" => family::<Wide>(name, fam, n, p),
            "gf32003" => family::<Zp32003>(name, fam, n, p),
            _ => family::<Zp2147483647>(name, fam, n, p),
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

fn input(field: &str, name: &str) -> Input {
    held_out(field, name).unwrap_or_else(|| {
        if ["gf32003", "m31"].contains(&field) {
            ladder(field, name)
        } else {
            wide(field, name)
        }
    })
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
        .unwrap_or_else(|| panic!("no frozen row {field}/{name}"));
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
        digest,
        variables: strings("variables"),
        generators: strings("generators"),
    }
}

fn sig_statistics(s: &SigF4Statistics) -> Json {
    let size = |v: usize| Json::size(v);
    Json::object([
        ("batches", size(s.batches)),
        ("pairs_created", size(s.pairs_created)),
        ("pairs_singular", size(s.pairs_singular)),
        ("rejected_product", size(s.rejected_product)),
        ("rejected_koszul", size(s.rejected_koszul)),
        ("rejected_zero_row", size(s.rejected_zero_row)),
        ("rejected_rewrite", size(s.rejected_rewrite)),
        ("rejected_duplicate", size(s.rejected_duplicate)),
        ("targets", size(s.targets)),
        ("reducer_rows", size(s.reducer_rows)),
        ("reductions_to_zero", size(s.reductions_to_zero)),
        ("zero_rows", size(s.zero_rows)),
        ("singular_rows", size(s.singular_rows)),
        ("rows_adding_no_rank", size(s.rows_adding_no_rank)),
        ("coefficient_products", Json::int(s.coefficient_products)),
        ("products_on_zero_rows", Json::int(s.products_on_zero_rows)),
        (
            "products_on_singular_rows",
            Json::int(s.products_on_singular_rows),
        ),
        ("max_matrix_rows", size(s.max_matrix_rows)),
        ("max_matrix_columns", size(s.max_matrix_columns)),
        ("elements_added", size(s.elements_added)),
        ("signature_basis_elements", size(s.signature_basis_elements)),
        ("reduced_basis_elements", size(s.reduced_basis_elements)),
        ("interreduction_columns", size(s.interreduction_columns)),
        ("interreduction_nonzeros", size(s.interreduction_nonzeros)),
        (
            "interreduction_peak_nonzeros",
            size(s.interreduction_peak_nonzeros),
        ),
        ("syzygy_signatures", size(s.syzygy_signatures)),
        ("peak_pending", size(s.peak_pending)),
        ("signature_metadata_bytes", size(s.signature_metadata_bytes)),
        ("bookkeeping_ns", Json::nanos(s.bookkeeping)),
        ("symbolic_ns", Json::nanos(s.symbolic)),
        ("elimination_ns", Json::nanos(s.elimination)),
        ("interreduction_ns", Json::nanos(s.interreduction)),
        ("total_ns", Json::nanos(s.total)),
        (
            "claim_announcement_waits",
            Json::int(s.claim_announcement_waits),
        ),
        ("claim_final_waits", Json::int(s.claim_final_waits)),
        ("claim_peak_live_bytes", size(s.claim_peak_live_bytes)),
        ("claim_phase_a_ns", Json::nanos(s.claim_phase_a)),
        ("claim_cascade_ns", Json::nanos(s.claim_cascade)),
        #[cfg(feature = "research-sigf4-split")]
        ("split", split(&s.split)),
        #[cfg(feature = "research-sigf4-usage")]
        ("usage", usage(&s.usage)),
    ])
}

/// #936: which signature-basis elements were consulted, and how; the syzygy-store replay.
#[cfg(feature = "research-sigf4-usage")]
fn usage(u: &zeebra::grobner::sigf4::usage::UsageReport) -> Json {
    use zeebra::grobner::sigf4::usage::ElementUse;
    let count =
        |f: &dyn Fn(&ElementUse) -> bool| Json::size(u.elements.iter().filter(|e| f(e)).count());
    let sum = |f: &dyn Fn(&ElementUse) -> u64| Json::int(u.elements.iter().map(f).sum::<u64>());
    let essential = |e: &ElementUse| e.dominated_from.is_none();
    let terms_read = |e: &ElementUse| e.reducer_rows + e.target_rows > 0;
    let consulted =
        |e: &ElementUse| terms_read(e) || e.partner_roles > 0 || e.rewriter_wins.get() > 0;
    let r = &u.replay;
    let batches = u.batches.iter().map(|b| {
        Json::object([
            ("degree", Json::int(b.degree)),
            ("targets", Json::size(b.targets)),
            ("elements_added", Json::size(b.elements_added)),
            ("essential_added", Json::size(b.essential_added)),
            ("select_ns", Json::nanos(b.select)),
            ("insert_ns", Json::nanos(b.insert)),
            ("symbolic_ns", Json::nanos(b.symbolic)),
            ("elimination_ns", Json::nanos(b.elimination)),
        ])
    });
    Json::object([
        ("elements", Json::size(u.elements.len())),
        ("essential", count(&essential)),
        ("dominated", count(&|e| !essential(e))),
        (
            "dominated_at_birth",
            count(&|e| e.dominated_from == Some(e.born)),
        ),
        ("never_consulted", count(&|e| !consulted(e))),
        ("terms_read", count(&terms_read)),
        (
            "dominated_terms_read_after",
            count(&|e| e.rows_after_dominated > 0),
        ),
        (
            "dominated_rewriter_won",
            count(&|e| !essential(e) && e.rewriter_wins.get() > 0),
        ),
        (
            "dominated_partner",
            count(&|e| !essential(e) && e.partner_roles > 0),
        ),
        ("reducer_rows", sum(&|e| e.reducer_rows)),
        (
            "reducer_rows_dominated",
            sum(&|e| if essential(e) { 0 } else { e.reducer_rows }),
        ),
        ("target_rows", sum(&|e| e.target_rows)),
        (
            "target_rows_dominated",
            sum(&|e| if essential(e) { 0 } else { e.target_rows }),
        ),
        ("rows_after_dominated", sum(&|e| e.rows_after_dominated)),
        ("partner_roles", sum(&|e| e.partner_roles)),
        ("rewriter_wins", sum(&|e| e.rewriter_wins.get())),
        ("terms", sum(&|e| e.terms as u64)),
        (
            "terms_dominated",
            sum(&|e| if essential(e) { 0 } else { e.terms as u64 }),
        ),
        (
            "terms_dominated_never_read_after",
            sum(&|e| {
                if !essential(e) && e.rows_after_dominated == 0 {
                    e.terms as u64
                } else {
                    0
                }
            }),
        ),
        ("rewriter_calls", Json::int(u.rewriter_calls.get())),
        ("rewriter_scanned", Json::int(u.rewriter_scanned.get())),
        ("rewriter_divisible", Json::int(u.rewriter_divisible.get())),
        ("reducer_lookups", Json::int(u.reducer_lookups)),
        ("reducer_scanned", Json::int(u.reducer_scanned)),
        ("minimal_selection_ns", Json::nanos(u.minimal_selection)),
        ("minimal_elements", Json::size(u.minimal_elements)),
        ("store_koszul_inserts", Json::size(r.koszul_inserts)),
        ("store_zero_row_inserts", Json::size(r.zero_row_inserts)),
        ("store_queries", Json::size(r.queries)),
        ("store_koszul_hits", Json::size(r.koszul_hits)),
        ("store_koszul_hits_equal", Json::size(r.koszul_hits_equal)),
        ("store_koszul_hits_lost", Json::size(r.koszul_hits_lost)),
        ("store_replay_full_ns", Json::nanos(r.full)),
        (
            "store_replay_without_koszul_ns",
            Json::nanos(r.without_koszul),
        ),
        ("store_koszul_skippable", Json::size(r.koszul_skippable)),
        ("store_replay_skip_covered_ns", Json::nanos(r.skip_covered)),
        ("batches", Json::Array(batches.collect())),
    ])
}

/// #901: per-batch reducer-block / cascade split and the engine's glue clocks.
#[cfg(feature = "research-sigf4-split")]
fn split(log: &zeebra::grobner::sigf4::SplitLog) -> Json {
    let batches = log.batches.iter().map(|b| {
        Json::object([
            ("targets", Json::size(b.targets)),
            ("reducers", Json::size(b.reducers)),
            ("columns", Json::size(b.columns)),
            ("entries", Json::int(b.entries)),
            ("setup_ns", Json::nanos(b.setup)),
            ("parallel_pass_ns", Json::nanos(b.parallel_pass)),
            ("serial_pass_ns", Json::nanos(b.serial_pass)),
            ("parallel_products", Json::int(b.parallel_products)),
            (
                "serial_reducer_products",
                Json::int(b.serial_reducer_products),
            ),
            ("cascade_products", Json::int(b.cascade_products)),
            ("cascading_targets", Json::size(b.cascading_targets)),
        ])
    });
    let symbolic = &log.symbolic;
    let sum = |f: fn(&zeebra::grobner::sigf4::SymbolicSplit) -> Duration| -> Duration {
        symbolic.iter().map(f).sum()
    };
    // Time-weighted over batches, each batch at the mean of its before and after readings.
    let read: Vec<(f64, f64)> = symbolic
        .iter()
        .filter_map(|b| {
            let khz = (b.khz_before? + b.khz_after?) as f64 / 2.0;
            Some((khz, b.total.as_secs_f64()))
        })
        .collect();
    let weight: f64 = read.iter().map(|r| r.1).sum();
    let khz = read.iter().map(|r| r.0 * r.1).sum::<f64>() / weight;
    let mut cpus: Vec<usize> = symbolic.iter().filter_map(|b| b.cpu).collect();
    cpus.sort_unstable();
    cpus.dedup();
    let symbolic = Json::object([
        ("total_ns", Json::nanos(sum(|b| b.total))),
        ("reducer_search_ns", Json::nanos(sum(|b| b.reducer_search))),
        ("multiply_ns", Json::nanos(sum(|b| b.multiply))),
        ("interning_ns", Json::nanos(sum(|b| b.interning))),
        ("column_sort_ns", Json::nanos(sum(|b| b.column_sort))),
        (
            "searches",
            Json::int(symbolic.iter().map(|b| b.searches).sum::<u64>()),
        ),
        (
            "terms",
            Json::int(symbolic.iter().map(|b| b.terms).sum::<u64>()),
        ),
        (
            "khz_weighted",
            if weight > 0.0 {
                Json::int(khz as u64)
            } else {
                Json::Null
            },
        ),
        (
            "cpus",
            Json::Array(cpus.into_iter().map(Json::size).collect()),
        ),
    ]);
    Json::object([
        ("symbolic", symbolic),
        ("inputs_ns", Json::nanos(log.inputs)),
        ("materialize_ns", Json::nanos(log.materialize)),
        ("drop_ns", Json::nanos(log.drop)),
        ("minimal_selection_ns", Json::nanos(log.minimal_selection)),
        ("redundant_elements", Json::size(log.redundant_elements)),
        (
            "products_on_redundant_elements",
            Json::int(log.products_on_redundant_elements),
        ),
        (
            "products_on_kept_elements",
            Json::int(log.products_on_kept_elements),
        ),
        ("batches", Json::Array(batches.collect())),
    ])
}

#[cfg(feature = "research-work")]
fn discovery(report: &zeebra::linalg::work::WorkReport) -> Json {
    let (mut forward, mut backward, mut zero_rows, mut zero_products) = (0u64, 0u64, 0u64, 0u64);
    for b in &report.batches {
        forward += b.forward.coefficient_products as u64;
        backward += b.backward.coefficient_products as u64;
        for r in &b.discovery {
            if r.completed && r.pivot_column.is_none() {
                zero_rows += 1;
                zero_products += (r.inherited_products + r.discovered_products) as u64;
            }
        }
    }
    Json::object([
        ("forward_products", Json::int(forward)),
        ("backward_products", Json::int(backward)),
        ("zero_rows", Json::int(zero_rows)),
        ("products_on_zero_rows", Json::int(zero_products)),
    ])
}

#[cfg(feature = "research-sigf4-replay")]
fn basis_sha256<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    names: &[&str; N],
) -> String {
    let mut text: Vec<_> = basis
        .iter()
        .map(|p| polynomial_to_string(p, names, ORDER))
        .collect();
    text.sort();
    sha256_hex(text.join("\n").as_bytes())
}

#[cfg(feature = "research-sigf4-replay")]
mod cascade {
    use super::*;
    use zeebra::grobner::sigf4::replay::{ceiling, record, BatchRecord, SCHEDULES};

    /// Every count the plan's validation names; timings excluded.
    fn algebraic(s: &SigF4Statistics) -> Vec<u64> {
        let counts = [
            s.batches,
            s.pairs_created,
            s.pairs_singular,
            s.rejected_product,
            s.rejected_koszul,
            s.rejected_zero_row,
            s.rejected_rewrite,
            s.rejected_duplicate,
            s.targets,
            s.reducer_rows,
            s.reductions_to_zero,
            s.singular_rows,
            s.elements_added,
            s.signature_basis_elements,
            s.reduced_basis_elements,
            s.syzygy_signatures,
        ];
        counts
            .iter()
            .map(|&v| v as u64)
            .chain([
                s.coefficient_products,
                s.products_on_zero_rows,
                s.products_on_singular_rows,
            ])
            .collect()
    }

    fn batch(r: &BatchRecord) -> Json {
        let int = |v: u64| Json::int(v);
        let size = |v: usize| Json::size(v);
        Json::object([
            ("columns", size(r.columns)),
            ("targets", size(r.targets)),
            ("zero_targets", size(r.zero_targets)),
            ("reducer_steps", int(r.reducer_steps)),
            ("target_steps", int(r.target_steps)),
            ("surviving", int(r.surviving)),
            ("shadowed", int(r.shadowed)),
            ("phase_a", int(r.phase_a)),
            ("max_phase_a", int(r.max_phase_a)),
            ("cascade", int(r.cascade)),
            ("max_target", int(r.max_target)),
            ("dependent_targets", size(r.dependent_targets)),
            ("edges", size(r.edges)),
            ("depth", size(r.depth)),
            ("width", size(r.width)),
            ("cp_dag", int(r.critical[0])),
            ("cp_frontier", int(r.critical[1])),
            ("cp_claim", int(r.critical[2])),
            ("would_displace", int(r.would_displace)),
            ("displaced_suffix", int(r.displaced_suffix)),
        ])
    }

    fn ratio(x: f64) -> Json {
        Json::string(format!("{x:.3}"))
    }

    /// Ceilings at 4/8/16 workers against design 1's products, per arm and schedule.
    fn ceilings(d1: &[BatchRecord], d2: &[BatchRecord]) -> Json {
        let base: u64 = d1.iter().map(BatchRecord::work).sum();
        let d2_work: u64 = d2.iter().map(BatchRecord::work).sum();
        let mut rows = Vec::new();
        for workers in [4, 8, 16] {
            let mut row = |arm: &str, schedule: &str, records: &[BatchRecord], s, work: u64| {
                let (bound, greedy) = ceiling(records, base, s, workers);
                rows.push(Json::object([
                    ("workers", Json::size(workers)),
                    ("arm", Json::string(arm)),
                    ("schedule", Json::string(schedule)),
                    ("ceiling", ratio(bound)),
                    ("greedy", ratio(greedy)),
                    ("products_ratio", ratio(work as f64 / base as f64)),
                ]));
            };
            for s in SCHEDULES {
                row("exact", s.name(), d1, Some(s), base);
                row("prereduce", s.name(), d2, Some(s), d2_work);
            }
            row("prereduce", "serial-cascade", d2, None, d2_work);
        }
        Json::Array(rows)
    }

    pub(super) fn report<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        names: &[&str; N],
        digest: &str,
        args: &Args,
    ) -> Json {
        let options = |workers| SigF4Options {
            max_wall_time: Some(args.wall),
            workers,
            ..SigF4Options::default()
        };
        let (plain, plain_stats) = sig_f4_reported(system, ORDER, &options(1));
        let ((d1, d1_stats), d1_records) = record(|| sig_f4_reported(system, ORDER, &options(1)));
        let ((d2, d2_stats), d2_records) =
            record(|| sig_f4_reported(system, ORDER, &options(args.workers)));
        let (plain, d1, d2) = (
            plain.expect("design 1 finishes"),
            d1.expect("recorded design 1 finishes"),
            d2.expect("recorded design 2 finishes"),
        );
        let digest_of = |b: &[MultivariatePolynomial<N, F>]| basis_sha256(b, names);
        assert_eq!(
            algebraic(&d1_stats),
            algebraic(&plain_stats),
            "recording moved an algebraic quantity"
        );
        assert_eq!(
            digest_of(&d1),
            digest_of(&plain),
            "recording moved the basis"
        );
        assert_eq!(
            digest_of(&d2),
            digest_of(&plain),
            "design 2 moved the basis"
        );
        let all = |records: &[BatchRecord]| Json::Array(records.iter().map(batch).collect());
        Json::object([
            ("field", Json::string(&args.field)),
            ("name", Json::string(&args.name)),
            ("digest", Json::string(digest)),
            ("design2_workers", Json::size(args.workers)),
            ("basis_sha256", Json::string(digest_of(&plain))),
            ("replay_invariant", Json::Bool(true)),
            ("design1_statistics", sig_statistics(&plain_stats)),
            ("design2_statistics", sig_statistics(&d2_stats)),
            ("ceilings", ceilings(&d1_records, &d2_records)),
            ("design1_batches", all(&d1_records)),
            ("design2_batches", all(&d2_records)),
        ])
    }
}

/// #933: every batch's symbolic closure replayed at 1/4/8/16 workers beside the engine's own.
#[cfg(feature = "research-sigf4-replay")]
mod closure {
    use super::*;
    use zeebra::grobner::sigf4::symbolic_replay::{record, SymbolicRecord};

    fn batch(r: &SymbolicRecord) -> Json {
        let runs = r.runs.iter().map(|run| {
            Json::object([
                ("workers", Json::size(run.workers)),
                ("total_ns", Json::int(run.total)),
                ("scan_ns", Json::int(run.scan)),
                ("merge_ns", Json::int(run.merge)),
                ("sort_ns", Json::int(run.sort)),
            ])
        });
        Json::object([
            ("targets", Json::size(r.targets)),
            ("rows", Json::size(r.rows)),
            ("columns", Json::size(r.columns)),
            ("serial_ns", Json::int(r.serial_ns)),
            ("lookup_ns", Json::int(r.census.lookup_ns)),
            (
                "levels",
                Json::Array(r.levels.iter().map(|&n| Json::size(n)).collect()),
            ),
            ("runs", Json::Array(runs.collect())),
        ])
    }

    pub(super) fn report<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        names: &[&str; N],
        digest: &str,
        args: &Args,
    ) -> Json {
        let options = SigF4Options {
            max_wall_time: Some(args.wall),
            workers: args.workers,
            parallel_cascade: args.claim,
            ..SigF4Options::default()
        };
        let (plain, plain_stats) = sig_f4_reported(system, ORDER, &options);
        let ((recorded, stats), records) = record(args.min_frontier, || {
            sig_f4_reported(system, ORDER, &options)
        });
        let digest_of = |b: Result<Vec<MultivariatePolynomial<N, F>>, _>| {
            basis_sha256(&b.expect("the engine finishes"), names)
        };
        let basis = digest_of(plain);
        assert_eq!(digest_of(recorded), basis, "recording moved the basis");
        let census = |f: fn(&SymbolicRecord) -> u64| Json::int(records.iter().map(f).sum::<u64>());
        Json::object([
            ("field", Json::string(&args.field)),
            ("name", Json::string(&args.name)),
            ("digest", Json::string(digest)),
            ("engine_workers", Json::size(args.workers)),
            ("claim", Json::Bool(args.claim)),
            ("min_frontier", Json::size(args.min_frontier)),
            ("basis_sha256", Json::string(basis)),
            ("plain_statistics", sig_statistics(&plain_stats)),
            ("recorded_symbolic_ns", Json::nanos(stats.symbolic)),
            ("lookup_ns", census(|r| r.census.lookup_ns)),
            ("cache_current", census(|r| r.census.cache_current)),
            ("cache_stale", census(|r| r.census.cache_stale)),
            ("cache_missing", census(|r| r.census.cache_missing)),
            ("elements_scanned", census(|r| r.census.elements_scanned)),
            ("batches", Json::Array(records.iter().map(batch).collect())),
        ])
    }
}

/// The basis from an engine independent of Zeebra's: Singular through its adapter, the pinned
/// groebner-rs driver, or the naive Buchberger reference in-process. External answers are parsed back and
/// made monic, so the digest is computed exactly as for Zeebra's own bases.
fn reference<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    input: &Input,
    args: &Args,
) -> Result<Vec<MultivariatePolynomial<N, F>>, String> {
    if args.engine == "reference" {
        return Ok(buchberger_reference(system, args.order));
    }
    let modulus: u64 = match args.field.as_str() {
        "goldilocks" => 18446744069414584321,
        "wide64" => 18446744073709551263,
        "gf32003" => 32003,
        _ => 2147483647,
    };
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let instance = Instance::new(
        &args.name,
        args.name.split('-').next().unwrap_or("row"),
        FieldSpec::prime(modulus),
        input.variables.clone(),
        system
            .iter()
            .map(|p| polynomial_to_string(p, &names, args.order))
            .collect(),
        args.order,
    );
    let scratch = std::path::PathBuf::from(std::env::var("TMPDIR").map_err(|_| "set TMPDIR")?)
        .join(format!("sig-f4-study-{}", std::process::id()));
    let texts: Vec<String> = if args.engine == "singular" {
        let mut solver = SingularSolver::with_binary("Singular", &scratch, args.wall)
            .map_err(|e| format!("{e:?}"))?;
        let limits = Limits::wall(args.wall).with_workers(args.workers);
        let report = solver.run(&instance, Task::ReducedGrobnerBasis, &limits);
        let answer = report
            .status
            .answer()
            .ok_or_else(|| format!("{:?}", report.status))?;
        answer.basis.clone().ok_or("no basis in the answer")?
    } else {
        groebner_rs(&instance, modulus, args, &scratch)?
    };
    let _ = std::fs::remove_dir_all(&scratch);
    texts
        .iter()
        .map(|text| {
            let p = MultivariatePolynomial::<N, F>::parse(text, names)
                .map_err(|e| format!("{text}: {e}"))?;
            Ok(p.scale(&p.leading_coefficient(args.order).inverse()))
        })
        .collect()
}

/// The pinned groebner-rs driver (`$ZEEBRA_GROEBNER_RS_DRIVER`) through its JSON contract 2 directly:
/// the adapter would also verify against Zeebra, which needs built-in widths these fields lack, and
/// the comparison here is the digest.
fn groebner_rs(
    instance: &Instance,
    modulus: u64,
    args: &Args,
    scratch: &std::path::Path,
) -> Result<Vec<String>, String> {
    let quoted = |list: &[String]| {
        list.iter()
            .map(|s| format!("\"{s}\""))
            .collect::<Vec<_>>()
            .join(",")
    };
    let order = if args.order == MonomialOrder::GradedLexicographic {
        "grlex"
    } else {
        "grevlex"
    };
    let request = format!(
        "{{\"variables\":[{}],\"modulus\":{modulus},\"order\":\"{order}\",\"workers\":{},\"generators\":[{}]}}",
        quoted(&instance.variables),
        args.workers,
        quoted(&instance.system)
    );
    std::fs::create_dir_all(scratch).map_err(|e| e.to_string())?;
    let path = scratch.join("groebner-rs.json");
    std::fs::write(&path, request).map_err(|e| e.to_string())?;
    let driver =
        std::env::var("ZEEBRA_GROEBNER_RS_DRIVER").unwrap_or_else(|_| "groebner-rs-driver".into());
    let output = std::process::Command::new(driver)
        .arg(&path)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let json = Json::parse(&String::from_utf8_lossy(&output.stdout)).map_err(|e| e.to_string())?;
    json.get("basis")
        .ok_or("no basis in the driver's output")?
        .items()
        .iter()
        .map(|t| {
            t.as_str()
                .map(str::to_string)
                .ok_or("a basis entry is not text".into())
        })
        .collect()
}

/// The most threads alive in this process at once during the solve, besides the main thread and
/// the sampler, read from `/proc/self/task` every 50 µs (#941's worker discipline check). A lower
/// bound: a thread that lives less than one interval can be missed.
struct ThreadSampler {
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    handle: std::thread::JoinHandle<usize>,
}

impl ThreadSampler {
    fn start() -> Self {
        use std::sync::atomic::Ordering;
        let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let flag = stop.clone();
        let handle = std::thread::spawn(move || {
            let mut peak = 0;
            while !flag.load(Ordering::Relaxed) {
                if let Ok(tasks) = std::fs::read_dir("/proc/self/task") {
                    peak = peak.max(tasks.count());
                }
                std::thread::sleep(Duration::from_micros(50));
            }
            peak.saturating_sub(2)
        });
        Self { stop, handle }
    }

    fn finish(self) -> usize {
        self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
        self.handle.join().expect("sampler")
    }
}

fn run<const N: usize, F: FiniteField>(input: Input, args: &Args) -> Json {
    let names: [&str; N] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<N, F>> = input
        .generators
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).expect("generator parses"))
        .collect();
    if args.symbolic {
        #[cfg(feature = "research-sigf4-replay")]
        return closure::report(&system, &names, &input.digest, args);
        #[cfg(not(feature = "research-sigf4-replay"))]
        panic!("--symbolic-replay requires --features research-sigf4-replay");
    }
    if args.replay {
        #[cfg(feature = "research-sigf4-replay")]
        return cascade::report(&system, &names, &input.digest, args);
        #[cfg(not(feature = "research-sigf4-replay"))]
        panic!("--replay requires --features research-sigf4-replay");
    }
    // `--repeat k` (#934): k solves in one process, the last one reported; `calls_ns` keeps every
    // call's time, the first of them cold.
    let mut calls = Vec::with_capacity(args.repeat);
    let solve = || {
        if args.engine == "adaptive" {
            let options = F4Options {
                graded_engine: GradedEngine::Adaptive,
                ..f4_options(args)
            };
            let (result, stats) = f4_reported(&system, args.order, &options);
            let route = stats.graded_route.as_ref();
            let summary = Json::object([
                (
                    "route",
                    Json::string(format!("{:?}", route.map(|r| &r.route))),
                ),
                (
                    "dispatch_ns",
                    route.map_or(Json::Null, |r| Json::nanos(r.dispatch)),
                ),
                ("team", route.map_or(Json::Null, |r| Json::size(r.workers))),
                (
                    "cascade",
                    Json::string(format!("{:?}", route.and_then(|r| r.cascade))),
                ),
                ("batches", Json::size(stats.batches)),
                ("elements_added", Json::size(stats.elements_added)),
                ("max_matrix_rows", Json::size(stats.max_matrix_rows)),
                ("max_matrix_columns", Json::size(stats.max_matrix_columns)),
            ]);
            (result.map_err(|e| e.to_string()), summary, Json::Null)
        } else if REFERENCES.contains(&args.engine.as_str()) {
            (reference(&system, &input, args), Json::Null, Json::Null)
        } else if args.engine == "entry" {
            let (result, report) = f4_signature_reported(&system, args.order, &f4_options(args));
            let summary = Json::object([
                ("route", Json::string(format!("{:?}", report.route))),
                ("dispatch_ns", Json::nanos(report.dispatch)),
                ("variables", Json::size(report.features.variables)),
                (
                    "min_nonlinear_degree",
                    Json::int(report.features.min_nonlinear_degree),
                ),
                ("max_degree", Json::int(report.features.max_degree)),
                ("terms", Json::size(report.features.terms)),
                ("monomials", Json::int(report.features.monomials)),
                ("field_bits", Json::int(report.features.field_bits)),
                ("max_workers", Json::size(report.features.workers)),
                ("team", Json::size(report.workers)),
                ("cascade", Json::string(format!("{:?}", report.cascade))),
            ]);
            (result.map_err(|e| e.to_string()), summary, Json::Null)
        } else if args.engine == "sigf4" {
            let options = SigF4Options {
                max_wall_time: Some(args.wall),
                workers: args.workers,
                parallel_cascade: args.claim,
                ..SigF4Options::default()
            };
            let (result, stats) = sig_f4_reported(&system, args.order, &options);
            (
                result.map_err(|e| e.to_string()),
                sig_statistics(&stats),
                Json::Null,
            )
        } else {
            let options = f4_options(args);
            let solve = || f4_reported(&system, args.order, &options);
            #[cfg(feature = "research-work")]
            let ((result, stats), work) = if args.discovery {
                let (r, w) = zeebra::linalg::work::measure_discovery(solve);
                (r, discovery(&w))
            } else {
                (solve(), Json::Null)
            };
            #[cfg(not(feature = "research-work"))]
            let ((result, stats), work) = {
                assert!(!args.discovery, "--discovery requires research-work");
                (solve(), Json::Null)
            };
            let summary = Json::object([
                ("batches", Json::size(stats.batches)),
                ("pairs_reduced", Json::size(stats.pairs_reduced)),
                ("zero_rows", Json::size(stats.zero_rows)),
                ("elements_added", Json::size(stats.elements_added)),
                ("max_matrix_rows", Json::size(stats.max_matrix_rows)),
                ("max_matrix_columns", Json::size(stats.max_matrix_columns)),
                (
                    "stages",
                    if args.stages {
                        f4_stage_statistics(&stats)
                    } else {
                        Json::Null
                    },
                ),
            ]);
            (result.map_err(|e| e.to_string()), summary, work)
        }
    };
    let threads = args.sample_threads.then(ThreadSampler::start);
    for _ in 1..args.repeat {
        let warm = Instant::now();
        drop(solve());
        calls.push(warm.elapsed());
    }
    let started = Instant::now();
    let (result, statistics, work) = solve();
    let elapsed = started.elapsed();
    let threads_peak = threads.map(ThreadSampler::finish);
    let m33 = Instant::now();
    let basis_m33 = result
        .as_ref()
        .ok()
        .map(|b| basis_digest::basis_digest(b, modulus(&args.field).into()));
    let m33 = m33.elapsed();
    let render = Instant::now();
    let (status, basis) = match &result {
        Ok(_) if args.digest_only => ("complete".to_string(), None),
        Ok(basis) => {
            let mut text: Vec<_> = basis
                .iter()
                .map(|p| polynomial_to_string(p, &names, args.order))
                .collect();
            text.sort();
            ("complete".to_string(), Some(text))
        }
        Err(error) => (format!("stopped: {error}"), None),
    };
    let render = render.elapsed();
    if let (Some(path), Some(text)) = (&args.write_basis, &basis) {
        std::fs::write(path, text.join("\n") + "\n").expect("--write-basis");
    }
    let certification = match (&result, args.certify) {
        (Ok(basis), true) => {
            let clock = Instant::now();
            // On the run's workers: serially, Eco-12's certificate outran its 600 s budget (#887).
            let report = certify_f4_output_with_workers(&system, basis, args.order, args.workers);
            Json::object([
                ("checks_passed", Json::Bool(report.checks_passed())),
                ("complete", Json::Bool(report.is_complete())),
                ("ns", Json::nanos(clock.elapsed())),
            ])
        }
        _ => Json::Null,
    };
    Json::object([
        ("field", Json::string(&args.field)),
        ("name", Json::string(&args.name)),
        ("digest", Json::string(&input.digest)),
        ("engine", Json::string(&args.engine)),
        ("workers", Json::size(args.workers)),
        ("status", Json::string(status)),
        ("call_ns", Json::nanos(elapsed)),
        (
            "calls_ns",
            Json::Array(
                calls
                    .iter()
                    .chain([&elapsed])
                    .map(|&d| Json::nanos(d))
                    .collect(),
            ),
        ),
        ("render_ns", Json::nanos(render)),
        ("basis_m33", basis_m33.map_or(Json::Null, Json::string)),
        ("basis_m33_ns", Json::nanos(m33)),
        ("threads_peak", threads_peak.map_or(Json::Null, Json::size)),
        (
            "peak_rss_bytes",
            peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
        ),
        (
            "basis_elements",
            result.as_ref().map_or(Json::Null, |b| Json::size(b.len())),
        ),
        (
            "basis_sha256",
            basis.as_ref().map_or(Json::Null, |b| {
                Json::string(sha256_hex(b.join("\n").as_bytes()))
            }),
        ),
        ("statistics", statistics),
        ("work", work),
        ("certification", certification),
    ])
}

fn main() {
    let started = Instant::now();
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = parse_args(&raw).unwrap_or_else(|e| panic!("{e}"));
    let input = if args.generate {
        generated(&args.field, &args.name).unwrap_or_else(|e| panic!("{e}"))
    } else {
        input(&args.field, &args.name)
    };
    let n = input.variables.len();
    if args.input_only {
        let strings = |v: &[String]| Json::Array(v.iter().map(Json::string).collect());
        let row = Json::object([
            ("field", Json::string(&args.field)),
            ("name", Json::string(&args.name)),
            ("modulus", Json::string(modulus(&args.field).to_string())),
            ("digest", Json::string(&input.digest)),
            ("variables", strings(&input.variables)),
            ("generators", strings(&input.generators)),
        ]);
        println!("{}", row.to_json().replace('\n', ""));
        return;
    }
    // Every field at every size a catalog, the ladder or `--generate` can produce.
    macro_rules! dispatch {
        ($($field:literal => $f:ty),*) => {
            match (args.field.as_str(), n) {
                $(
                    ($field, 4) => run::<4, $f>(input, &args),
                    ($field, 6) => run::<6, $f>(input, &args),
                    ($field, 7) => run::<7, $f>(input, &args),
                    ($field, 8) => run::<8, $f>(input, &args),
                    ($field, 9) => run::<9, $f>(input, &args),
                    ($field, 10) => run::<10, $f>(input, &args),
                    ($field, 11) => run::<11, $f>(input, &args),
                    ($field, 12) => run::<12, $f>(input, &args),
                    ($field, 13) => run::<13, $f>(input, &args),
                    ($field, 14) => run::<14, $f>(input, &args),
                )*
                (field, n) => panic!("no instantiation for {field} with {n} variables"),
            }
        };
    }
    let mut report = dispatch!(
        "goldilocks" => Goldilocks, "wide64" => Wide, "gf32003" => Zp32003, "m31" => Zp2147483647
    );
    // In-process time before and after the solve: with `call_ns` and `render_ns` this leaves only
    // exec and exit to the caller's process wall.
    if let Json::Object(fields) = &mut report {
        fields.push(("main_ns".into(), Json::nanos(started.elapsed())));
    }
    println!("{}", report.to_json().replace('\n', ""));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Result<Args, String> {
        parse_args(&list.iter().map(|s| s.to_string()).collect::<Vec<_>>())
    }

    // Both engines take workers, the census is serial-F4-only, and unknown fields or engines fail.
    #[test]
    fn arguments_are_validated() {
        let base = ["--field", "wide64", "--name", "eco-12", "--engine"];
        assert!(args(&[&base[..], &["sigf4"]].concat()).is_ok());
        assert!(args(&[&base[..], &["sigf4", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[&base[..], &["f4", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[&base[..], &["f4", "--workers", "16", "--discovery"]].concat()).is_err());
        // #972/#918: stage measurement and the FL order configure the shipping F4 only.
        assert!(args(&[&base[..], &["f4", "--workers", "4", "--stages", "--fl"]].concat()).is_ok());
        assert!(args(&[&base[..], &["sigf4", "--stages"]].concat()).is_err());
        assert!(args(&[&base[..], &["entry", "--fl"]].concat()).is_err());
        let fewest = args(&[&base[..], &["f4", "--reducer", "FewestTerms"]].concat()).unwrap();
        assert_eq!(fewest.reducer, ReducerSelection::FewestTerms);
        assert!(args(&[&base[..], &["f4", "--reducer", "Sparsest"]].concat()).is_err());
        assert!(args(&[&base[..], &["magma"]].concat()).is_err());
        assert!(args(&["--field", "bn254", "--name", "eco-12", "--engine", "f4"]).is_err());
        assert!(args(&[&base[..], &["entry", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[
            "--field",
            "m31",
            "--name",
            "mq-random-10",
            "--engine",
            "entry"
        ])
        .is_ok());
    }

    // The option arm and the reference engines parse, under either graded order, and references are never repeated or certified.
    #[test]
    fn adaptive_arm_references_and_orders_parse() {
        let base = ["--field", "m31", "--name", "katsura-10", "--engine"];
        let parsed = args(&[&base[..], &["adaptive", "--order", "grlex"]].concat()).unwrap();
        assert_eq!(parsed.order, MonomialOrder::GradedLexicographic);
        assert_eq!(args(&[&base[..], &["f4"]].concat()).unwrap().order, ORDER);
        for engine in REFERENCES {
            assert!(args(&[&base[..], &[engine]].concat()).is_ok());
            assert!(args(&[&base[..], &[engine, "--repeat", "3"]].concat()).is_err());
            assert!(args(&[&base[..], &[engine, "--certify"]].concat()).is_err());
        }
        assert!(args(&[&base[..], &["f4", "--order", "lex"]].concat()).is_err());
    }

    // `--repeat` takes a positive count and times the solve alone, so it refuses the add-ons.
    #[test]
    fn repeat_times_the_solve_alone() {
        let base = [
            "--field",
            "wide64",
            "--name",
            "katsura-4",
            "--engine",
            "entry",
        ];
        assert_eq!(
            args(&[&base[..], &["--repeat", "5"]].concat())
                .unwrap()
                .repeat,
            5
        );
        assert!(args(&[&base[..], &["--repeat", "0"]].concat()).is_err());
        assert!(args(&[&base[..], &["--repeat", "5", "--certify"]].concat()).is_err());
    }

    // The replay runs both signature designs, so it needs the signature engine and two workers.
    #[test]
    fn replay_needs_the_signature_engine_and_two_workers() {
        let base = [
            "--field", "wide64", "--name", "eco-12", "--replay", "--engine",
        ];
        assert!(args(&[&base[..], &["sigf4", "--workers", "2"]].concat()).is_ok());
        assert!(args(&[&base[..], &["sigf4"]].concat()).is_err());
        assert!(args(&[&base[..], &["f4", "--workers", "2"]].concat()).is_err());
    }

    // The symbolic replay needs the signature engine and is not the cascade replay.
    #[test]
    fn symbolic_replay_needs_the_signature_engine() {
        let base = ["--field", "wide64", "--name", "eco-12", "--symbolic-replay"];
        let sig = |extra: &[&str]| args(&[&base[..], &["--engine", "sigf4"], extra].concat());
        assert_eq!(sig(&["--min-frontier", "64"]).unwrap().min_frontier, 64);
        assert!(sig(&["--workers", "16", "--claim"]).is_ok());
        assert!(sig(&["--workers", "2", "--replay"]).is_err());
        assert!(args(&[&base[..], &["--engine", "f4"]].concat()).is_err());
    }

    // The parallel cascade belongs to the signature engine and is not a replay arm.
    #[test]
    fn claim_needs_the_signature_engine() {
        let base = [
            "--field", "wide64", "--name", "eco-12", "--claim", "--engine",
        ];
        assert!(args(&[&base[..], &["sigf4", "--workers", "16"]].concat()).is_ok());
        assert!(args(&[&base[..], &["f4", "--workers", "16"]].concat()).is_err());
        assert!(args(&[&base[..], &["sigf4", "--workers", "2", "--replay"]].concat()).is_err());
    }

    // The shipping F4 arm caps the symbolic team at the worker count, as forward is (#883).
    #[test]
    fn f4_arm_caps_the_symbolic_team() {
        use zeebra::grobner::ParallelSymbolic;
        let base = ["--field", "wide64", "--name", "eco-12", "--engine", "f4"];
        let one = f4_options(&args(&base).unwrap());
        assert_eq!(one.parallel_symbolic, ParallelSymbolic::Serial);
        let four = f4_options(&args(&[&base[..], &["--workers", "4"]].concat()).unwrap());
        assert_eq!(
            four.parallel_symbolic,
            ParallelSymbolic::Auto { max_workers: 4 }
        );
    }

    // Every #939 held-out candidate builds from its source and reproduces its pinned SHA-256.
    #[test]
    fn held_out_candidates_reproduce_their_pins() {
        for (field, name, pinned) in HELD_OUT {
            assert_eq!(input(field, name).digest, pinned, "{field}/{name}");
        }
    }

    /// `--generate` reproduces every row M32 pinned in the external contract's form, MQ at seed n.
    #[test]
    fn generated_rows_reproduce_the_code_pins() {
        let pins = [
            ("m31", "katsura-10", HELD_OUT[3].2),
            ("m31", "eco-11", HELD_OUT[4].2),
            ("goldilocks", "cyclic-6", HELD_OUT[5].2),
            ("gf32003", "mq-random-9-s9", HELD_OUT[2].2),
            (
                "gf32003",
                "mq-random-10-s10",
                "16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f",
            ),
        ];
        for (field, name, pinned) in pins {
            assert_eq!(
                generated(field, name).unwrap().digest,
                pinned,
                "{field}/{name}"
            );
        }
    }

    /// `--generate` refuses a family it has no generator for and an unseeded MQ row.
    #[test]
    fn generate_refuses_unknown_rows() {
        assert!(generated("m31", "bivium-3").is_err());
        assert!(generated("m31", "mq-random-10").is_err());
        assert!(generated("m31", "katsura-40").is_err());
    }

    // The two engines agree on a small frozen row, which is what the basis digest relies on.
    #[test]
    fn engines_agree_on_katsura_4() {
        let run_engine = |engine: &str| {
            let a = args(&[
                "--field",
                "goldilocks",
                "--name",
                "katsura-4",
                "--engine",
                engine,
            ])
            .unwrap();
            run::<4, Goldilocks>(wide("goldilocks", "katsura-4"), &a)
                .get("basis_sha256")
                .and_then(Json::as_str)
                .map(str::to_string)
        };
        assert!(run_engine("sigf4").is_some());
        assert_eq!(run_engine("sigf4"), run_engine("f4"));
    }
}
