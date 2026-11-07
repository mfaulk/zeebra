//! Self-consistency checks on the committed table of Fukuoka MQ Challenge solves.
//!
//! The fixture is a transcription of 37 web pages, and a transcription rots silently: a swapped `n`
//! and `m`, a dropped digit in a runtime, a per-subsystem figure relabelled as a total all look
//! plausible. So these checks re-derive rather than parse. `m = 2n` and `n = floor(1.5m)` come from
//! the challenge's own generator source (`docs/research/fukuoka-mq.md` §4), the coefficient count
//! comes from the crate's own importer, and the published runtimes are checked against their own
//! published parts — the block-Wiedemann phase times against their total, and a hybrid attack's
//! total against its subsystem count and average.
//!
//! Nothing here downloads, solves, or measures anything.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use zeebra::grobner::research::MqInstance;

/// One recorded solve.
#[derive(Debug)]
struct Solve {
    challenge_type: String,
    n: u64,
    m: u64,
    seed: u64,
    date: String,
    contestants: String,
    figure_kind: String,
    runtime_seconds: f64,
    phases_seconds: Option<f64>,
    peak_gb: Option<f64>,
    peak_metric: String,
    subsystems: Option<f64>,
    avg_subsystem_seconds: Option<f64>,
    processes: Option<f64>,
    answer_published: String,
    details: String,
}

impl Solve {
    /// How a failure names the row, so a message points at a page rather than a line number.
    fn label(&self) -> String {
        format!(
            "type {} n={} m={} seed={} ({}, {})",
            self.challenge_type, self.n, self.m, self.seed, self.date, self.details
        )
    }
}

const COLUMNS: usize = 19;

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("research/fukuoka-mq/solved-instances.tsv")
}

/// `-` is the fixture's "not published", and must not become `0`.
fn optional(field: &str, column: &str, label: &str) -> Option<f64> {
    if field == "-" {
        return None;
    }
    Some(
        field
            .replace(',', "")
            .parse()
            .unwrap_or_else(|e| panic!("{label}: column {column} is {field:?}, not a number: {e}")),
    )
}

fn load() -> Vec<Solve> {
    let path = fixture_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));

    text.lines()
        .filter(|line| !line.trim_start().starts_with('#') && !line.trim().is_empty())
        .map(|line| {
            let f: Vec<&str> = line.split('\t').collect();
            assert_eq!(
                f.len(),
                COLUMNS,
                "row starting {:?} has {} tab-separated fields, expected {COLUMNS}",
                f.first().unwrap_or(&""),
                f.len()
            );
            let label = format!("{} n={} seed={}", f[0], f[1], f[3]);
            Solve {
                challenge_type: f[0].to_string(),
                n: f[1].parse().expect("n"),
                m: f[2].parse().expect("m"),
                seed: f[3].parse().expect("seed"),
                date: f[4].to_string(),
                contestants: f[5].to_string(),
                figure_kind: f[8].to_string(),
                runtime_seconds: optional(f[9], "runtime_seconds", &label)
                    .unwrap_or_else(|| panic!("{label}: runtime_seconds is required")),
                phases_seconds: optional(f[10], "phases_seconds", &label),
                peak_gb: optional(f[11], "peak_gb", &label),
                peak_metric: f[12].to_string(),
                subsystems: optional(f[13], "subsystems", &label),
                avg_subsystem_seconds: optional(f[14], "avg_subsystem_seconds", &label),
                processes: optional(f[15], "processes", &label),
                answer_published: f[16].to_string(),
                details: f[17].to_string(),
            }
        })
        .collect()
}

/// The fixture holds every recorded solve of the four types it covers, and nothing else.
#[test]
fn test_the_fixture_covers_the_four_types_and_nothing_else() {
    let solves = load();
    assert_eq!(solves.len(), 37, "expected 37 recorded solves");
    let types: BTreeSet<&str> = solves.iter().map(|s| s.challenge_type.as_str()).collect();
    assert_eq!(
        types,
        BTreeSet::from(["II", "III", "V", "VI"]),
        "types I and IV are #197's, not this fixture's"
    );
    let mut per_type: BTreeMap<&str, usize> = BTreeMap::new();
    for s in &solves {
        *per_type.entry(s.challenge_type.as_str()).or_default() += 1;
    }
    assert_eq!(per_type["II"], 6);
    assert_eq!(per_type["III"], 8);
    assert_eq!(per_type["V"], 12);
    assert_eq!(per_type["VI"], 11);
}

/// The encryption families are overdetermined with exactly `m = 2n`, as their generator fixes.
#[test]
fn test_the_encryption_families_have_m_equal_to_twice_n() {
    for s in load().iter().filter(|s| matches!(s.challenge_type.as_str(), "II" | "III")) {
        assert_eq!(
            s.m,
            2 * s.n,
            "{}: the encryption generator sets m = 2n, so m should be {}",
            s.label(),
            2 * s.n
        );
    }
}

/// The signature families are underdetermined with `n = floor(1.5 m)` — the generator's own
/// `n = m * 1.5` truncated, not rounded, which is why `m = 17` gives `n = 25` and not 26.
#[test]
fn test_the_signature_families_have_n_equal_to_the_truncation_of_one_and_a_half_m() {
    for s in load().iter().filter(|s| matches!(s.challenge_type.as_str(), "V" | "VI")) {
        let expected = (s.m * 3) / 2;
        assert_eq!(
            s.n,
            expected,
            "{}: the signature generator sets n = (int)(m * 1.5), so n should be {expected}",
            s.label()
        );
    }
}

/// Every row's variable count agrees with the importer about how many coefficients a polynomial
/// carries, and that count is the binomial the challenge generator uses.
#[test]
fn test_the_coefficient_count_is_the_binomial_the_generator_uses() {
    for s in load() {
        let n = s.n as usize;
        // The generator's `binomial_coef(n + 2, 2)`.
        let binomial = (n + 2) * (n + 1) / 2;
        assert_eq!(
            MqInstance::coefficients_per_polynomial(n),
            binomial,
            "{}: the importer and the generator disagree on the coefficient count",
            s.label()
        );
        // And the same number as quadratic + linear + constant, which is how a reader thinks of it.
        assert_eq!(binomial, n * (n + 1) / 2 + n + 1, "{}", s.label());
    }
}

/// Where a solve publishes its block-Wiedemann phase times, they account for its reported total.
///
/// The tolerance is 0.1%: several phase times are printed only to whole minutes or to two decimal
/// places in days, so exact agreement is not available even when the figures are right.
#[test]
fn test_published_phase_times_account_for_the_published_total() {
    let mut checked = 0;
    for s in load() {
        let Some(phases) = s.phases_seconds else {
            continue;
        };
        let relative = (phases - s.runtime_seconds).abs() / s.runtime_seconds;
        assert!(
            relative < 0.001,
            "{}: phases sum to {phases} s but the total is {} s, off by {:.3}%",
            s.label(),
            s.runtime_seconds,
            relative * 100.0
        );
        checked += 1;
    }
    assert_eq!(checked, 6, "six rows publish a phase breakdown");
}

/// Where a hybrid attack publishes a total, a subsystem count, a per-subsystem average and the
/// number of simultaneous processes, those four agree.
///
/// This is the check that catches a transposed digit in any one of them, because all four have to
/// agree at once. The three rows that qualify agree to better than 0.004%, so the tolerance is
/// 0.1% — tight enough that transposing two adjacent digits of a four-figure average fails it.
///
/// Three rows are excluded by the fixture itself, by carrying no process count: the 2025 type VI
/// pair, where no integer process count reconciles the published numbers at all, and the 2023
/// type VI row, whose total exceeds its derived value by 2.6%. See
/// `docs/research/fukuoka-mq.md` §9.
#[test]
fn test_a_hybrid_attacks_total_follows_from_its_subsystems_and_its_parallelism() {
    let mut checked = 0;
    for s in load() {
        if s.figure_kind != "wall-total" {
            continue;
        }
        let (Some(subsystems), Some(average), Some(processes)) =
            (s.subsystems, s.avg_subsystem_seconds, s.processes)
        else {
            continue;
        };
        let derived = subsystems * average / processes;
        let relative = (derived - s.runtime_seconds).abs() / s.runtime_seconds;
        assert!(
            relative < 0.001,
            "{}: {subsystems} subsystems x {average} s / {processes} processes = {derived} s, \
             but the reported total is {} s, off by {:.2}%",
            s.label(),
            s.runtime_seconds,
            relative * 100.0
        );
        checked += 1;
    }
    assert_eq!(checked, 3, "three wall-total rows publish all three ingredients");
}

/// The two rows that publish a peak-memory figure name which metric it is.
///
/// `VmHWM` and `VmPeak` are different numbers for the same run — resident high-water mark against
/// peak virtual size — so a figure without its metric is not comparable with anything, including
/// with `src/util/peak_memory.rs`. Pinned because the pair is the whole published evidence on
/// memory for these four types.
#[test]
fn test_the_published_memory_figures_carry_their_metric() {
    let mut found = Vec::new();
    for s in load() {
        match (s.peak_gb, s.peak_metric.as_str()) {
            (None, "-") => {}
            (Some(gb), metric) => {
                assert!(
                    matches!(metric, "VmHWM" | "VmPeak"),
                    "{}: {gb} GB is recorded without a recognized metric ({metric:?})",
                    s.label()
                );
                found.push((s.challenge_type.clone(), s.n, gb, metric.to_string()));
            }
            (None, metric) => panic!("{}: metric {metric:?} with no figure", s.label()),
        }
    }
    assert_eq!(
        found,
        vec![
            ("III".to_string(), 36, 29.77, "VmHWM".to_string()),
            ("III".to_string(), 38, 49.45, "VmPeak".to_string()),
        ]
    );
}

/// The rows whose figure is per-subsystem rather than a total are exactly the five known ones.
///
/// Pinned by name because the distinction is invisible in the number itself: 370 seconds looks like
/// a fast solve and is in fact the cost of one of an unstated number of subsystems. A future edit
/// that relabelled one of these as `wall-total` would make it quotable as a record time.
#[test]
fn test_the_per_subsystem_figures_are_exactly_the_known_ones() {
    let flagged: BTreeSet<String> = load()
        .iter()
        .filter(|s| s.figure_kind != "wall-total")
        .map(|s| format!("{} m={} seed={}", s.challenge_type, s.m, s.seed))
        .collect();
    assert_eq!(
        flagged,
        BTreeSet::from([
            "V m=16 seed=2".to_string(),
            "V m=17 seed=1".to_string(),
            "V m=18 seed=4".to_string(),
            "V m=19 seed=0".to_string(),
            "V m=19 seed=4".to_string(),
        ]),
        "the set of per-subsystem figures changed"
    );
    for s in load() {
        assert!(
            matches!(
                s.figure_kind.as_str(),
                "wall-total" | "per-subsystem-cpu" | "per-subsystem-wall"
            ),
            "{}: unknown figure_kind {:?}",
            s.label(),
            s.figure_kind
        );
    }
}

/// No `(type, n, seed)` is recorded twice, and no `n` carries more than the five rows rule 2 allows.
#[test]
fn test_the_rows_obey_the_challenges_own_recording_rules() {
    let mut seen: BTreeSet<(String, u64, u64)> = BTreeSet::new();
    let mut per_size: BTreeMap<(String, u64), usize> = BTreeMap::new();
    for s in load() {
        let key = (s.challenge_type.clone(), s.n, s.seed);
        assert!(seen.insert(key.clone()), "{}: recorded twice", s.label());
        let count = per_size
            .entry((s.challenge_type.clone(), s.n))
            .or_default();
        *count += 1;
        assert!(
            *count <= 5,
            "{}: rule 2 records at most five solves per n, found {count}",
            s.label()
        );
    }
}

/// The largest recorded solve of each type is the record the write-up quotes.
///
/// Types II and III are ranked by `n`, types V and VI by `m`, which is why the two are compared on
/// different columns — swapping them is precisely the mistake this pins.
#[test]
fn test_the_record_per_type_is_the_one_the_write_up_quotes() {
    let solves = load();
    let best = |t: &str, by_n: bool| -> (u64, String, String) {
        let s = solves
            .iter()
            .filter(|s| s.challenge_type == t)
            .max_by_key(|s| if by_n { s.n } else { s.m })
            .expect("at least one row");
        (
            if by_n { s.n } else { s.m },
            s.date.clone(),
            s.contestants.clone(),
        )
    };
    assert_eq!(
        best("II", true),
        (38, "2026-09-28".into(), "Javier Verbel".into())
    );
    assert_eq!(
        best("III", true),
        (
            38,
            "2020-08-03".into(),
            "Tung Chou, Ruben Niederhagen, Bo-Yin Yang".into()
        )
    );
    assert_eq!(
        best("V", false),
        (21, "2026-09-17".into(), "Ting Li, Yao Sun".into())
    );
    assert_eq!(
        best("VI", false),
        (24, "2025-10-16".into(), "Kosuke Sakata, Tsuyoshi Takagi".into())
    );
}

/// Every recorded solve publishes its answer vector, so every row is a fetchable witness.
#[test]
fn test_every_recorded_solve_publishes_an_answer_vector() {
    for s in load() {
        assert_eq!(
            s.answer_published,
            "yes",
            "{}: the write-up claims every recorded solve is a usable witness",
            s.label()
        );
        assert!(
            s.details.starts_with("details/details_"),
            "{}: details path {:?} is not fetchable from the challenge site",
            s.label(),
            s.details
        );
    }
}
