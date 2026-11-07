//! Shape and self-consistency checks on the committed Courtois MinRank parameter table.
//!
//! The fixture is a transcription of a 2001 paper's table, and a transcription is exactly the kind
//! of artifact that rots silently: a wrong `q`, a transposed `n` and `r`, a dropped digit in an
//! attack exponent all look plausible. The checks below are therefore not "does the file parse" —
//! they re-derive the `Pr_alpha[Rank <= r]` column from the paper's *own* formula for `m_max`
//! (section 10) and require the derivation to reproduce what is printed. That ties `q`, `eta`, `n`,
//! `m` and `r` together, so corrupting any one of them fails a test rather than quietly changing
//! what a future surrogate generator builds.
//!
//! Nothing here solves, generates, or measures anything. The fixture holds parameters; no authentic
//! challenge instance exists. See `docs/research/minrank.md`.

use std::path::PathBuf;

/// One row of the published parameter table.
#[derive(Debug)]
struct Challenge {
    id: String,
    q: u64,
    eta: u64,
    n: u64,
    m: u64,
    r: u64,
    pr_solution: String,
    comm_kb_20x: f64,
    /// Brute force, Kernel, Big m, Syndrome, Sub-matrices, MQ — base-2 logs, `None` for the
    /// paper's infinity sign.
    attacks: [Option<u64>; 6],
}

const ATTACK_NAMES: [&str; 6] = [
    "brute force",
    "kernel",
    "big m",
    "syndrome",
    "sub-matrices",
    "MQ",
];

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("research/minrank/courtois-challenges.tsv")
}

fn load() -> Vec<Challenge> {
    let path = fixture_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));

    text.lines()
        .filter(|line| !line.trim_start().starts_with('#') && !line.trim().is_empty())
        .map(|line| {
            let f: Vec<&str> = line.split('\t').collect();
            assert_eq!(
                f.len(),
                14,
                "row {:?} has {} tab-separated fields, expected 14",
                f.first().unwrap_or(&""),
                f.len()
            );

            let num = |i: usize| -> u64 {
                f[i].parse()
                    .unwrap_or_else(|e| panic!("row {}: field {i} ({:?}) is not an integer: {e}", f[0], f[i]))
            };
            let attack = |i: usize| -> Option<u64> {
                if f[i] == "inf" {
                    None
                } else {
                    Some(f[i].parse().unwrap_or_else(|e| {
                        panic!("row {}: attack field {i} ({:?}) is neither an integer nor \"inf\": {e}", f[0], f[i])
                    }))
                }
            };

            Challenge {
                id: f[0].to_string(),
                q: num(1),
                eta: num(2),
                n: num(3),
                m: num(4),
                r: num(5),
                pr_solution: f[6].to_string(),
                comm_kb_20x: f[7]
                    .parse()
                    .unwrap_or_else(|e| panic!("row {}: comm_kb_20x {:?} is not a number: {e}", f[0], f[7])),
                attacks: [
                    attack(8),
                    attack(9),
                    attack(10),
                    attack(11),
                    attack(12),
                    attack(13),
                ],
            }
        })
        .collect()
}

impl Challenge {
    /// Courtois section 10: `m_max = eta*n + r^2 - (eta+n)*r + 1`, the largest `m` at which one
    /// solution is expected on average.
    fn m_max(&self) -> i64 {
        (self.eta * self.n) as i64 + (self.r * self.r) as i64
            - ((self.eta + self.n) * self.r) as i64
            + 1
    }

    /// Base-2 log of the expected number of non-collinear solutions, from the same section:
    /// `((q^m - 1)/(q - 1)) * q^-((eta-r)(n-r))` for the square case the challenges use.
    fn expected_solutions_log2(&self) -> f64 {
        let log2q = (self.q as f64).log2();
        let defect = (self.n - self.r) * (self.eta - self.r);
        self.m as f64 * log2q - defect as f64 * log2q - ((self.q - 1) as f64).log2()
    }
}

/// The fixture contains exactly the six published challenges, A through F, each appearing once.
#[test]
fn the_table_holds_challenges_a_through_f() {
    let rows = load();
    let ids: Vec<&str> = rows.iter().map(|c| c.id.as_str()).collect();
    assert_eq!(
        ids,
        ["A", "B", "C", "D", "E", "F"],
        "the published table has six parameter sets A-F, in that order"
    );
}

/// Every row declares a square matrix shape with a target rank strictly below it, over one of the
/// two fields the paper names.
#[test]
fn every_row_declares_a_usable_shape() {
    for c in load() {
        assert_eq!(
            c.eta, c.n,
            "{}: the paper's A-F all use square matrices (eta == n)",
            c.id
        );
        assert!(
            c.r < c.n,
            "{}: the paper requires r < n, got r={} n={}",
            c.id,
            c.r,
            c.n
        );
        assert!(c.m >= 1, "{}: needs at least one matrix M_1", c.id);
        assert!(
            c.q == 2 || c.q == 65521,
            "{}: the paper works 'either over GF(2) or over GF(65521)', got q={}",
            c.id,
            c.q
        );
        assert!(
            c.comm_kb_20x > 0.0,
            "{}: communication cost must be positive, got {}",
            c.id,
            c.comm_kb_20x
        );
    }
}

/// A, B and C are over GF(65521) and D, E, F over GF(2), as the table's `q` row prints them.
#[test]
fn the_prime_field_challenges_are_exactly_a_b_and_c() {
    let prime: Vec<String> = load()
        .into_iter()
        .filter(|c| c.q == 65521)
        .map(|c| c.id)
        .collect();
    assert_eq!(
        prime,
        ["A", "B", "C"],
        "65521 is the largest prime below 2^16 and the paper uses it only for A-C"
    );
}

/// No challenge exceeds Courtois's own `m_max`, and A, B and C sit exactly on it.
#[test]
fn the_unknown_count_respects_the_papers_m_max() {
    for c in load() {
        assert!(
            (c.m as i64) <= c.m_max(),
            "{}: m={} exceeds m_max={}, so the instance would be expected to have no solution \
             structure the paper claims",
            c.id,
            c.m,
            c.m_max()
        );
        if c.q == 65521 {
            assert_eq!(
                c.m as i64,
                c.m_max(),
                "{}: the prime-field challenges are placed exactly at m_max",
                c.id
            );
        }
    }
}

/// The printed `Pr_alpha[Rank <= r]` column is reproduced by the paper's own expected-solution
/// count, which ties q, eta, n, m and r together: corrupt any one and this fails.
#[test]
fn the_solution_probability_column_is_reproduced_from_the_parameters() {
    for c in load() {
        let exponent = c.expected_solutions_log2().round() as i64;
        match c.pr_solution.as_str() {
            // One solution expected on average gives 1 - 1/e = 0.63, printed as 0.6.
            "0.6" => assert_eq!(
                exponent, 0,
                "{}: printed Pr 0.6 needs ~2^0 expected solutions, parameters give 2^{}",
                c.id, exponent
            ),
            // Below one expected solution the probability is the expectation itself.
            other => {
                let printed: i64 = other
                    .strip_prefix("2^")
                    .unwrap_or_else(|| panic!("{}: unrecognised Pr column {:?}", c.id, other))
                    .parse()
                    .unwrap_or_else(|e| {
                        panic!("{}: unrecognised Pr exponent in {:?}: {e}", c.id, other)
                    });
                assert_eq!(
                    exponent, printed,
                    "{}: printed Pr 2^{} disagrees with the 2^{} the parameters give",
                    c.id, printed, exponent
                );
            }
        }
    }
}

/// The kernel attack is the cheapest finite attack on every one of A-F, which is what the source
/// asserts in bold and in prose.
#[test]
fn the_kernel_attack_is_the_best_known_on_every_challenge() {
    for c in load() {
        let kernel = c.attacks[1].unwrap_or_else(|| panic!("{}: kernel cost must be finite", c.id));
        for (i, cost) in c.attacks.iter().enumerate() {
            if i == 1 {
                continue;
            }
            if let Some(cost) = cost {
                assert!(
                    kernel < *cost,
                    "{}: kernel 2^{} is not cheaper than {} 2^{}, but the paper bolds kernel as the \
                     best attack",
                    c.id,
                    kernel,
                    ATTACK_NAMES[i],
                    cost
                );
            }
        }
    }
}

/// Sub-matrices and MQ are infinite on all of A-F; the paper says both "work only if r << n", which
/// these parameters deliberately avoid.
#[test]
fn the_two_small_rank_attacks_do_not_apply_to_any_challenge() {
    for c in load() {
        for i in [4usize, 5] {
            assert!(
                c.attacks[i].is_none(),
                "{}: the {} attack is printed as infinite for every one of A-F",
                c.id,
                ATTACK_NAMES[i]
            );
        }
    }
}

/// Challenge D's row matches the only published instance file carrying these parameters: a 19x19
/// GF(2) instance of 82 matrices (M_0 plus M_1..M_81) at target rank 10.
#[test]
fn challenge_d_matches_the_shape_of_the_one_published_instance() {
    let d = load()
        .into_iter()
        .find(|c| c.id == "D")
        .expect("challenge D must be in the table");

    // Header line of paper_instance/instance.txt in the Cryptanalysis of MinRank 2.0 artifact,
    // sha256 2fc12a0d52fc2523e773153b50b1b643b545506b2181b63505ec1d6ab084bda9: "19 19 81 10",
    // followed by 1558 rows of 19 GF(2) entries. See docs/research/minrank.md section 5.3.
    let (rows, cols, unknowns, rank, body_lines) = (19u64, 19u64, 81u64, 10u64, 1558u64);

    assert_eq!((d.eta, d.n, d.m, d.r), (rows, cols, unknowns, rank));
    assert_eq!(d.q, 2, "the published instance is over GF(2)");
    assert_eq!(
        body_lines,
        (d.m + 1) * d.eta,
        "the instance carries m + 1 = {} matrices of {} rows, because the formulation subtracts M_0",
        d.m + 1,
        d.eta
    );
}
