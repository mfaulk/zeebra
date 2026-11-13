use std::{
    mem::size_of,
    time::{Duration, Instant},
};
use zeebra::{
    fields::Zp32003 as F,
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4::{build_batch_matrix, reduce_batch, CacheMode, MonicBasis, ReducerCache},
        interreduce_for_benchmark,
        pairs::{CriterionCounts, PairQueue},
        F4Error, F4Options,
    },
    util::{peak_resident_bytes, sha256_hex, Json},
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

const ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

#[derive(Clone)]
struct StudyOptions {
    solver: F4Options,
    adaptive: bool,
    max_retries: usize,
    deadline: Duration,
}
impl Default for StudyOptions {
    fn default() -> Self {
        Self {
            solver: F4Options::default(),
            adaptive: true,
            max_retries: 32,
            deadline: Duration::from_secs(60),
        }
    }
}
#[derive(Debug)]
struct Failure {
    kind: &'static str,
    detail: String,
}
impl Failure {
    fn new(kind: &'static str, detail: impl ToString) -> Self {
        Self {
            kind,
            detail: detail.to_string(),
        }
    }
}
#[derive(Debug)]
struct Attempt {
    selected: usize,
    pairs: usize,
    rows: usize,
    columns: usize,
    entries: usize,
    entry_capacity: usize,
    symbolic_row_capacity: usize,
    symbolic_handle_capacity: usize,
    simultaneous_queue_payload_lower_bound: usize,
    pending: usize,
    handled_before: usize,
    handled_trial: usize,
    preflight_nanos: u128,
    reduction_nanos: u128,
    status: String,
}
struct Run<const N: usize> {
    basis: Result<Vec<MultivariatePolynomial<N, F>>, Failure>,
    attempts: Vec<Attempt>,
    retries: usize,
    final_nanos: u128,
    elapsed_nanos: u128,
}
#[derive(Debug)]
struct Trial<const N: usize> {
    queue: PairQueue<N>,
    pairs: Vec<zeebra::grobner::pairs::CriticalPair<N>>,
    attempt: Attempt,
}

fn normalized<const N: usize>(
    input: &[MultivariatePolynomial<N, F>],
) -> Vec<MultivariatePolynomial<N, F>> {
    let mut basis = Vec::new();
    for p in input.iter().filter(|p| !p.is_zero()) {
        let p = p.scale(&p.leading_coefficient(ORDER).inverse());
        if !basis.contains(&p) {
            basis.push(p);
        }
    }
    basis
}
fn initial<const N: usize>(
    input: &[MultivariatePolynomial<N, F>],
    options: &F4Options,
) -> (MonicBasis<N, F>, PairQueue<N>, Vec<Monomial<N>>) {
    let basis = MonicBasis::new(&normalized(input), ORDER);
    let leads: Vec<_> = basis.leading_monomials().collect();
    let terms: Vec<_> = (0..basis.len())
        .map(|i| basis.element(i).terms.len())
        .collect();
    let queue = PairQueue::seeded_from_leads_ranked(
        &leads,
        &terms,
        &options.criteria,
        options.schedule,
        ORDER,
        &mut CriterionCounts::default(),
    );
    (basis, queue, leads)
}

// Queue and filtering changes remain private until construction and reduction both succeed.
fn trial<const N: usize>(
    basis: &MonicBasis<N, F>,
    committed: &PairQueue<N>,
    leads: &[Monomial<N>],
    cap: Option<usize>,
    options: &F4Options,
) -> Result<Trial<N>, (F4Error, Box<Attempt>)> {
    let start = Instant::now();
    let mut queue = committed.clone();
    let selected = queue.select_batch(cap);
    let count = selected.len();
    let pairs = queue.filter_batch(
        selected,
        leads,
        &options.criteria,
        &mut CriterionCounts::default(),
    );
    let a = committed.footprint();
    let b = queue.footprint();
    let payload = |x: zeebra::grobner::pairs::PairQueueFootprint| {
        x.heap_entries * size_of::<zeebra::grobner::pairs::CriticalPair<N>>()
            + (x.removed + x.handled) * size_of::<(usize, usize)>()
            + x.deferred * size_of::<zeebra::grobner::pairs::CriticalPair<N>>()
    };
    let mut attempt = Attempt {
        selected: count,
        pairs: pairs.len(),
        rows: 0,
        columns: 0,
        entries: 0,
        entry_capacity: 0,
        symbolic_row_capacity: 0,
        symbolic_handle_capacity: 0,
        simultaneous_queue_payload_lower_bound: payload(a) + payload(b),
        pending: a.live + a.deferred,
        handled_before: a.handled,
        handled_trial: b.handled,
        preflight_nanos: 0,
        reduction_nanos: 0,
        status: "filtered".into(),
    };
    if !pairs.is_empty() {
        let mut cache = ReducerCache::new(CacheMode::Off);
        match build_batch_matrix(basis, &pairs, ORDER, options, &mut cache) {
            Ok(built) => {
                attempt.rows = built.matrix.num_rows();
                attempt.columns = built.matrix.num_columns();
                attempt.entries = built.matrix.nonzeros();
                attempt.entry_capacity = built.matrix.matrix().entry_capacity();
                attempt.symbolic_row_capacity = built.preprocessed.rows.capacity();
                attempt.symbolic_handle_capacity = built.preprocessed.term_handles.capacity();
                attempt.status = "built".into();
                // All coefficient/symbolic attempt allocations die before rebuilding for reduction.
                drop(built);
            }
            Err(error) => {
                attempt.status = format!("construction-refusal: {error}");
                attempt.preflight_nanos = start.elapsed().as_nanos();
                return Err((error, Box::new(attempt)));
            }
        }
    }
    attempt.preflight_nanos = start.elapsed().as_nanos();
    Ok(Trial {
        queue,
        pairs,
        attempt,
    })
}
fn recoverable(error: F4Error) -> bool {
    matches!(
        error,
        F4Error::TooManyRows { .. }
            | F4Error::TooManyColumns { .. }
            | F4Error::TooManyNonzeros { .. }
            | F4Error::TooManyLiveBytes { .. }
    )
}
fn run<const N: usize>(input: &[MultivariatePolynomial<N, F>], options: &StudyOptions) -> Run<N> {
    let at = Instant::now();
    let mut result = Run {
        basis: Ok(Vec::new()),
        attempts: Vec::new(),
        retries: 0,
        final_nanos: 0,
        elapsed_nanos: 0,
    };
    result.basis = solve(
        input,
        options,
        at,
        &mut result.attempts,
        &mut result.retries,
        &mut result.final_nanos,
    );
    result.elapsed_nanos = at.elapsed().as_nanos();
    result
}
fn solve<const N: usize>(
    input: &[MultivariatePolynomial<N, F>],
    options: &StudyOptions,
    at: Instant,
    attempts: &mut Vec<Attempt>,
    retries: &mut usize,
    final_nanos: &mut u128,
) -> Result<Vec<MultivariatePolynomial<N, F>>, Failure> {
    if options.solver.max_pairs_per_batch == Some(0)
        || options.solver.reducer_cache != CacheMode::Off
        || options.solver.hilbert.is_active()
    {
        return Err(Failure::new(
            "options",
            "prototype requires positive cap, cache Off and Hilbert Off",
        ));
    }
    let mut basis = normalized(input);
    let (mut monic, mut pending, mut leads) = initial(input, &options.solver);
    if options
        .solver
        .max_basis_elements
        .is_some_and(|limit| basis.len() > limit)
    {
        return Err(Failure::new(
            "basis-limit",
            "initial basis exceeds allowance",
        ));
    }
    let mut batches = 0;
    while pending.has_work() {
        if at.elapsed() >= options.deadline {
            return Err(Failure::new("deadline", "before selection"));
        }
        if pending.is_empty() {
            pending.promote_deferred();
            continue;
        }
        let mut cap = options.solver.max_pairs_per_batch;
        loop {
            if at.elapsed() >= options.deadline {
                return Err(Failure::new("deadline", "before retry"));
            }
            match trial(&monic, &pending, &leads, cap, &options.solver) {
                Err((error, attempt)) => {
                    let selected = attempt.selected;
                    attempts.push(*attempt);
                    if !options.adaptive || !recoverable(error) {
                        return Err(Failure::new("construction", error));
                    }
                    if *retries >= options.max_retries {
                        return Err(Failure::new("retry-limit", error));
                    }
                    if selected <= 1 {
                        return Err(Failure::new("one-pair", error));
                    }
                    *retries += 1;
                    cap = Some((selected / 2).max(1));
                }
                Ok(mut trial) => {
                    if at.elapsed() >= options.deadline {
                        trial.attempt.status = "uncommitted-deadline-after-construction".into();
                        attempts.push(trial.attempt);
                        return Err(Failure::new("deadline", "after construction"));
                    }
                    if trial.pairs.is_empty() {
                        pending = trial.queue;
                        attempts.push(trial.attempt);
                        break;
                    }
                    if options
                        .solver
                        .max_batches
                        .is_some_and(|limit| batches >= limit)
                    {
                        trial.attempt.status = "uncommitted-batch-limit".into();
                        attempts.push(trial.attempt);
                        return Err(Failure::new("batch-limit", "no reduction committed"));
                    }
                    let start = Instant::now();
                    // Fresh cache on both passes makes this the same matrix, at a measured rebuild cost.
                    let outcome = reduce_batch(&monic, &trial.pairs, ORDER, &options.solver);
                    trial.attempt.reduction_nanos = start.elapsed().as_nanos();
                    let outcome = match outcome {
                        Ok(outcome) => outcome,
                        Err(error) => {
                            trial.attempt.status = format!("reduction-refusal: {error}");
                            attempts.push(trial.attempt);
                            return Err(Failure::new("reduction", error));
                        }
                    };
                    assert_eq!(
                        (
                            trial.attempt.rows,
                            trial.attempt.columns,
                            trial.attempt.entries
                        ),
                        (
                            outcome.statistics.rows,
                            outcome.statistics.columns,
                            outcome.statistics.elimination.initial_nonzeros
                        )
                    );
                    trial.attempt.status = "reduced-uncommitted".into();
                    if at.elapsed() >= options.deadline {
                        trial.attempt.status = "uncommitted-deadline-after-reduction".into();
                        attempts.push(trial.attempt);
                        return Err(Failure::new("deadline", "after reduction before commit"));
                    }
                    trial.attempt.status = "committed".into();
                    attempts.push(trial.attempt);
                    pending = trial.queue;
                    batches += 1;
                    for candidate in outcome.candidates {
                        monic.push(&candidate, ORDER);
                        leads.push(candidate.leading_monomial(ORDER));
                        pending.push_term_count(candidate.terms().len());
                        basis.push(candidate);
                        if options
                            .solver
                            .max_basis_elements
                            .is_some_and(|limit| basis.len() > limit)
                        {
                            return Err(Failure::new("basis-limit", "candidate insertion"));
                        }
                        pending.push_pairs_from_leads(
                            &leads,
                            basis.len() - 1,
                            &options.solver.criteria,
                            &mut CriterionCounts::default(),
                        );
                    }
                    break;
                }
            }
        }
    }
    if at.elapsed() >= options.deadline {
        return Err(Failure::new("deadline", "before final interreduction"));
    }
    drop(pending);
    drop(monic);
    drop(leads);
    let final_at = Instant::now();
    let answer = interreduce_for_benchmark(basis, ORDER);
    *final_nanos = final_at.elapsed().as_nanos();
    if at.elapsed() >= options.deadline {
        return Err(Failure::new("deadline", "after final interreduction"));
    }
    Ok(answer)
}

fn attempt_json(a: &Attempt) -> Json {
    let built = a.rows != 0;
    let count = |n| if built { Json::size(n) } else { Json::Null };
    Json::object([
        ("selected", Json::size(a.selected)),
        ("filtered_pairs", Json::size(a.pairs)),
        ("rows", count(a.rows)),
        ("columns", count(a.columns)),
        ("entries", count(a.entries)),
        ("entry_capacity", count(a.entry_capacity)),
        ("symbolic_row_capacity", count(a.symbolic_row_capacity)),
        (
            "symbolic_handle_capacity",
            count(a.symbolic_handle_capacity),
        ),
        (
            "simultaneous_queue_payload_lower_bound",
            Json::size(a.simultaneous_queue_payload_lower_bound),
        ),
        ("queue_capacity_bytes", Json::Null),
        ("pending_before", Json::size(a.pending)),
        ("handled_before", Json::size(a.handled_before)),
        ("handled_trial", Json::size(a.handled_trial)),
        ("preflight_ns", Json::int(a.preflight_nanos as i128)),
        (
            "reduction_with_rebuild_ns",
            Json::int(a.reduction_nanos as i128),
        ),
        ("status", Json::string(&a.status)),
    ])
}
fn render<const N: usize>(
    basis: &[MultivariatePolynomial<N, F>],
    variables: &[String],
) -> Vec<String> {
    basis
        .iter()
        .map(|p| {
            zeebra::grobner::differential::polynomial_to_string(
                p,
                &variables.iter().map(String::as_str).collect::<Vec<_>>(),
                ORDER,
            )
        })
        .collect()
}
fn singular_reference<const N: usize>(
    system: &[String],
    variables: &[String],
) -> Result<Vec<MultivariatePolynomial<N, F>>, Box<dyn std::error::Error>> {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let script = format!("ring r=32003,({}),dp; short=0; option(redSB); ideal i={}; ideal g=std(i); int k; for(k=1;k<=size(g);k++){{print(\"@poly \"+string(g[k]));}} print(\"@done\"); quit;", variables.join(","), system.join(","));
    let mut child = Command::new("timeout")
        .args(["10s", "Singular", "-q"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child.stdin.take().unwrap().write_all(script.as_bytes())?;
    let output = child.wait_with_output()?;
    let text = String::from_utf8(output.stdout)?;
    if !output.status.success() || !text.contains("@done") || text.contains('?') {
        return Err(format!("Singular failed: {text}").into());
    }
    let vars: [&str; N] = variables
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| "arity")?;
    let mut answer = text
        .lines()
        .filter_map(|s| s.strip_prefix("@poly "))
        .map(|s| MultivariatePolynomial::parse(s, vars))
        .collect::<Result<Vec<_>, _>>()?;
    answer.retain(|p| !p.is_zero());
    answer.sort_by(|a, b| ORDER.cmp(&b.leading_monomial(ORDER), &a.leading_monomial(ORDER)));
    Ok(answer)
}
fn execute<const N: usize>(
    name: &str,
    input: Vec<MultivariatePolynomial<N, F>>,
    policy: &str,
    kind: &str,
    allowance: usize,
    max_retries: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let variables: Vec<String> = (1..=N).map(|i| format!("x{i}")).collect();
    let system = render(&input, &variables);
    let instance = zeebra::grobner::external::Instance::new(
        name,
        "batch-splitting-study",
        zeebra::grobner::external::FieldSpec::prime(32003),
        variables.clone(),
        system.clone(),
        ORDER,
    );
    let mut options = StudyOptions {
        max_retries,
        ..Default::default()
    };
    options.solver.max_wall_time = Some(options.deadline);
    options.solver.measure_stages = true;
    options.adaptive = policy == "adaptive";
    options.solver.max_pairs_per_batch = match policy {
        "static1" => Some(1),
        "static2" => Some(2),
        "adaptive" | "static-none" | "shipping" => None,
        _ => return Err("policy must be shipping|static-none|static1|static2|adaptive".into()),
    };
    match kind {
        "rows" => options.solver.max_matrix_rows = allowance,
        "columns" => options.solver.max_matrix_columns = allowance,
        "entries" => options.solver = options.solver.with_live_entries::<F>(allowance),
        "unbounded" => {
            options.solver.max_matrix_rows = usize::MAX;
            options.solver.max_matrix_columns = usize::MAX;
            options.solver.max_live_nonzeros = usize::MAX;
            options.solver.max_live_bytes = usize::MAX;
        }
        _ => return Err("budget must be rows|columns|entries|unbounded".into()),
    }
    let run = if policy == "shipping" {
        let start = Instant::now();
        let (basis, stats) = zeebra::grobner::f4_reported(&input, ORDER, &options.solver);
        Run {
            basis: basis.map_err(|error| Failure::new("shipping", error)),
            attempts: Vec::new(),
            retries: 0,
            elapsed_nanos: start.elapsed().as_nanos(),
            final_nanos: stats.stages.interreduction.as_nanos(),
        }
    } else {
        run(&input, &options)
    };
    let verify_start = Instant::now();
    let expected = singular_reference::<N>(&system, &variables)?;
    let expected_strings = render(&expected, &variables);
    let (status, failure, basis, verified) = match &run.basis {
        Ok(basis) => {
            let checks = zeebra::grobner::certify_submitted_basis(&input, basis, ORDER);
            if !checks.checks_passed() || *basis != expected {
                return Err(
                    "basis differs from exact Singular reference or submitted-basis checks fail"
                        .into(),
                );
            }
            // Equality to the independently computed complete basis supplies reverse inclusion.
            ("complete", Json::Null, render(basis, &variables), true)
        }
        Err(error) => (
            "refused",
            Json::object([
                ("kind", Json::string(error.kind)),
                ("detail", Json::string(&error.detail)),
            ]),
            Vec::new(),
            false,
        ),
    };
    let verification_ns = verify_start.elapsed().as_nanos();
    println!(
        "{}",
        Json::object([
            ("fixture", Json::string(name)),
            ("input_digest", Json::string(instance.digest())),
            (
                "variables",
                Json::Array(variables.iter().map(Json::string).collect())
            ),
            (
                "input",
                Json::Array(system.iter().map(Json::string).collect())
            ),
            ("policy", Json::string(policy)),
            ("budget_kind", Json::string(kind)),
            ("allowance", Json::size(allowance)),
            ("max_retries", Json::size(max_retries)),
            ("status", Json::string(status)),
            ("failure", failure),
            (
                "basis",
                Json::Array(basis.iter().map(Json::string).collect())
            ),
            (
                "reference_basis",
                Json::Array(expected_strings.iter().map(Json::string).collect())
            ),
            (
                "reference_digest",
                Json::string(sha256_hex(expected_strings.join("\n").as_bytes()))
            ),
            ("exact_reference_and_submitted_checks", Json::Bool(verified)),
            ("solve_ns", Json::int(run.elapsed_nanos as i128)),
            (
                "final_interreduction_ns",
                Json::int(run.final_nanos as i128)
            ),
            ("verification_ns", Json::int(verification_ns as i128)),
            ("retries", Json::size(run.retries)),
            (
                "attempts",
                Json::Array(run.attempts.iter().map(attempt_json).collect())
            ),
            (
                "process_peak_rss_bytes",
                peak_resident_bytes().map(Json::int).unwrap_or(Json::Null)
            ),
        ])
        .to_json()
    );
    Ok(())
}
fn random_mq() -> Vec<MultivariatePolynomial<3, F>> {
    let instance = zeebra::grobner::external::corpus::random_mq_instance(3, 0, 32003, ORDER);
    let variables: [&str; 3] = instance
        .variables
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    instance
        .system
        .iter()
        .map(|p| MultivariatePolynomial::parse(p, variables).unwrap())
        .collect()
}
fn homogenized<const N: usize, const M: usize>(
    input: Vec<MultivariatePolynomial<N, F>>,
) -> Vec<MultivariatePolynomial<M, F>> {
    assert_eq!(M, N + 1);
    input
        .iter()
        .map(|p| {
            let degree = p.degree() as u32;
            let terms: Vec<_> = p
                .terms()
                .iter()
                .map(|(m, c)| {
                    let mut exponents = [0; M];
                    exponents[..N].copy_from_slice(m.exponents());
                    exponents[N] = degree - m.degree() as u32;
                    (Monomial::new(&exponents), *c)
                })
                .collect();
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() < 4 || args.len() > 5 {
        return Err(
            "usage: batch_splitting_study FIXTURE POLICY BUDGET ALLOWANCE [MAX_RETRIES<=32]".into(),
        );
    }
    let allowance = args[3].parse()?;
    let retries = args.get(4).map(|s| s.parse()).transpose()?.unwrap_or(32);
    if retries > 32 {
        return Err("at most 32 retries".into());
    }
    match args[0].as_str() {
        "cyclic-3" => execute(
            &args[0],
            cyclic::<3, F>(),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "cyclic-4" => execute(
            &args[0],
            cyclic::<4, F>(),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "cyclic-homogeneous-4" => execute(
            &args[0],
            homogenized::<4, 5>(cyclic::<4, F>()),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "katsura-homogeneous-3" => execute(
            &args[0],
            homogenized::<4, 5>(katsura::<4, F>()),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "katsura-2" => execute(
            &args[0],
            katsura::<3, F>(),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "katsura-3" => execute(
            &args[0],
            katsura::<4, F>(),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "mq-random-3" => execute(
            &args[0],
            random_mq(),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "mq-homogeneous-3" => execute(
            &args[0],
            homogenized::<3, 4>(random_mq()),
            &args[1],
            &args[2],
            allowance,
            retries,
        ),
        "unit" | "positive-dimensional" => {
            let input = if args[0] == "unit" {
                vec!["1", "x1+x2"]
            } else {
                vec!["x1*x2", "x1*x3"]
            };
            execute(
                &args[0],
                input
                    .iter()
                    .map(|s| MultivariatePolynomial::<3, F>::parse(s, ["x1", "x2", "x3"]).unwrap())
                    .collect(),
                &args[1],
                &args[2],
                allowance,
                retries,
            )
        }
        _ => Err("unknown fixture".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // A failed construction trial never changes the committed queue or its handled witnesses.
    #[test]
    fn failed_trial_is_transactional() {
        let input = cyclic::<3, F>();
        let (basis, queue, leads) = initial(&input, &F4Options::default());
        let before = queue.footprint();
        let options = F4Options {
            max_matrix_rows: 0,
            ..Default::default()
        };
        assert!(trial(&basis, &queue, &leads, None, &options).is_err());
        assert_eq!(queue.footprint(), before);
    }

    // A one-pair construction refusal terminates without returning a partial basis.
    #[test]
    fn impossible_and_retry_exhaustion_refuse() {
        let input = katsura::<3, F>();
        let mut options = StudyOptions::default();
        options.solver.max_matrix_rows = 0;
        let result = run(&input, &options);
        assert!(result.basis.is_err());
        assert!(result.attempts.len() <= 33);
        options.max_retries = 0;
        assert_eq!(run(&input, &options).basis.unwrap_err().kind, "retry-limit");
    }

    // A zero deadline refuses before constructing or committing any pair batch.
    #[test]
    fn deadline_precedes_first_attempt() {
        let options = StudyOptions {
            deadline: std::time::Duration::ZERO,
            ..Default::default()
        };
        let result = run(&cyclic::<3, F>(), &options);
        assert_eq!(result.basis.unwrap_err().kind, "deadline");
        assert!(result.attempts.is_empty());
    }

    // All scheduling controls return the exact shipping basis with duplicates and zero generators.
    #[test]
    fn controls_and_replay_agree() {
        let mut input = cyclic::<3, F>();
        input.push(input[0].clone());
        input.push(MultivariatePolynomial::new::<(Monomial<3>, F)>(&[]));
        let expected = zeebra::grobner::f4(&input, ORDER).unwrap();
        for cap in [None, Some(1), Some(2)] {
            let mut options = StudyOptions::default();
            options.solver.max_pairs_per_batch = cap;
            let first = run(&input, &options);
            assert_eq!(first.basis.unwrap(), expected);
            let second = run(&input, &options);
            assert_eq!(
                first
                    .attempts
                    .iter()
                    .map(|a| (a.selected, a.rows, a.columns))
                    .collect::<Vec<_>>(),
                second
                    .attempts
                    .iter()
                    .map(|a| (a.selected, a.rows, a.columns))
                    .collect::<Vec<_>>()
            );
        }
    }
    // Smaller construction attempts recover at least one refused public-family solve under identical rows.
    #[test]
    fn lowered_row_budget_recovers() {
        let mut recovered = 0;
        for input in [cyclic::<4, F>(), katsura::<4, F>()] {
            let expected = zeebra::grobner::f4(&input, ORDER).unwrap();
            for rows in 1..=80 {
                let mut options = StudyOptions::default();
                options.solver.max_matrix_rows = rows;
                let adaptive = run(&input, &options);
                if let (Ok(answer), true) = (adaptive.basis, adaptive.retries > 0) {
                    options.adaptive = false;
                    assert_eq!(
                        run(&input, &options).basis.unwrap_err().kind,
                        "construction"
                    );
                    assert_eq!(answer, expected);
                    eprintln!("recovered rows={rows}");
                    recovered += 1;
                    break;
                }
            }
        }
        assert!(recovered > 0);
    }

    // Deferred obligations survive snapshot rollback and are promoted in the original tie order.
    #[test]
    fn rollback_preserves_deferred_and_tie_order() {
        let input = katsura::<4, F>();
        let (basis, mut queue, leads) = initial(&input, &F4Options::default());
        let first = queue.next_degree().unwrap();
        queue.defer_degree(first);
        let before = queue.footprint();
        let sequence = |queue: &PairQueue<4>| {
            let mut copy = queue.clone();
            copy.promote_deferred();
            let mut all = Vec::new();
            while copy.has_work() {
                all.extend(copy.select_batch(None));
            }
            all
        };
        let expected = sequence(&queue);
        queue.promote_deferred();
        let options = F4Options {
            max_matrix_rows: 0,
            ..Default::default()
        };
        assert!(trial(&basis, &queue, &leads, Some(1), &options).is_err());
        assert_eq!(sequence(&queue), expected);
        assert_eq!(queue.footprint().handled, before.handled);
    }

    // Unit and positive-dimensional ideals remain exact with chain filtering enabled and duplicates present.
    #[test]
    fn unit_positive_dimension_and_chain_controls() {
        let parse = |s| MultivariatePolynomial::<3, F>::parse(s, ["x", "y", "z"]).unwrap();
        for input in [
            vec![parse("1"), parse("x+y")],
            vec![parse("x*y"), parse("x*z"), parse("x*y")],
        ] {
            let expected = zeebra::grobner::f4(&input, ORDER).unwrap();
            for cap in [None, Some(1), Some(2)] {
                let mut options = StudyOptions::default();
                options.solver.criteria.gebauer_moller = false;
                options.solver.criteria.chain = true;
                options.solver.max_pairs_per_batch = cap;
                assert_eq!(run(&input, &options).basis.unwrap(), expected);
            }
        }
    }

    // Failed full-batch selections cannot create chain witnesses for a later smaller selection.
    #[test]
    fn failed_trial_preserves_chain_obligations() {
        let parse = |s| MultivariatePolynomial::<3, F>::parse(s, ["x", "y", "z"]).unwrap();
        let input = [parse("x"), parse("y"), parse("x*y")];
        let mut options = F4Options {
            criteria: zeebra::grobner::pairs::PairCriteria {
                product: false,
                chain: true,
                gebauer_moller: false,
            },
            ..Default::default()
        };
        let (basis, queue, leads) = initial(&input, &options);
        let before = queue.clone().select_batch(None);
        options.max_matrix_rows = 0;
        assert!(trial(&basis, &queue, &leads, None, &options).is_err());
        let after = queue.clone().select_batch(None);
        assert_eq!(before, after);
        assert_eq!(queue.footprint().handled, 0);
        options.max_matrix_rows = 100;
        let resumed = trial(&basis, &queue, &leads, Some(1), &options).unwrap();
        assert_eq!(resumed.pairs.len(), 1);
        assert_eq!(resumed.pairs[0], before[0]);
        assert_eq!(resumed.queue.footprint().handled, 1);
    }

    // Snapshot selection respects lazy Gebauer–Möller removals after a successful new leading monomial.
    #[test]
    fn snapshot_respects_stale_pairs() {
        let parse = |s| MultivariatePolynomial::<3, F>::parse(s, ["x", "y", "z"]).unwrap();
        let input = [parse("x^2*z"), parse("y^2*z"), parse("x*y")];
        let mut options = F4Options::default();
        options.criteria.product = false;
        let basis = MonicBasis::new(&input, ORDER);
        let leads: Vec<_> = basis.leading_monomials().collect();
        let mut queue = PairQueue::new();
        let mut counts = CriterionCounts::default();
        queue.push_pairs_from_leads(&leads, 1, &options.criteria, &mut counts);
        queue.push_pairs_from_leads(&leads, 2, &options.criteria, &mut counts);
        assert_eq!(queue.footprint().removed, 1);
        let selected = trial(&basis, &queue, &leads, None, &options).unwrap();
        assert!(selected.pairs.iter().all(|p| (p.left, p.right) != (0, 1)));
        assert_eq!(queue.len(), 2);
    }

    // Every homogeneous public-family transform returns the same independently derived shipping basis.
    #[test]
    fn homogeneous_family_controls() {
        for input in [
            homogenized::<4, 5>(cyclic::<4, F>()),
            homogenized::<4, 5>(katsura::<4, F>()),
        ] {
            let expected = zeebra::grobner::f4(&input, ORDER).unwrap();
            assert_eq!(
                run(&input, &StudyOptions::default()).basis.unwrap(),
                expected
            );
        }
        let input = homogenized::<3, 4>(random_mq());
        assert_eq!(
            run(&input, &StudyOptions::default()).basis.unwrap(),
            zeebra::grobner::f4(&input, ORDER).unwrap()
        );
    }

    // A built attempt remains observable when a batch cap refuses reduction before commitment.
    #[test]
    fn batch_limit_retains_uncommitted_attempt() {
        let mut options = StudyOptions::default();
        options.solver.max_batches = Some(0);
        let result = run(&cyclic::<3, F>(), &options);
        assert_eq!(result.basis.unwrap_err().kind, "batch-limit");
        assert_eq!(result.attempts.len(), 1);
        assert!(result.attempts[0].rows > 0);
        assert_eq!(result.attempts[0].status, "uncommitted-batch-limit");
    }

    // Elimination refusals are terminal even when their error type also occurs during construction.
    #[test]
    fn elimination_failure_is_not_retried() {
        let input = cyclic::<4, F>();
        let options = StudyOptions {
            solver: F4Options::default().with_live_entries::<F>(19),
            ..Default::default()
        };
        let result = run(&input, &options);
        assert_eq!(result.basis.unwrap_err().kind, "reduction");
        assert_eq!(result.retries, 0);
        assert!(result
            .attempts
            .last()
            .unwrap()
            .status
            .starts_with("reduction-refusal:"));
    }
}
