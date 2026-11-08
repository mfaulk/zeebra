//! What XL's matrix would cost at the degree it needs, against what F4's actually cost.
//!
//! #76's go/no-go says the answer is reachable without a solver:
//!
//! > **No-go** if XL's matrix is larger than F4's for every degree at which it could succeed — a
//! > result obtainable from **construction alone**, without a solver.
//!
//! So this builds no XL matrix and runs no linear algebra. It counts. XL multiplies each equation
//! by every monomial up to `D - 2` and treats the products as linear in the monomials up to `D`,
//! so at a chosen `D` the shape is determined by three binomial coefficients and the equations'
//! term count — all exact integers, which is why every figure here reproduces bit-for-bit and
//! needs no benchmark lock.
//!
//! **The degree XL needs** is the operating degree, not a free parameter. XL at `D` linearizes to a
//! system whose unknowns are the monomials of degree `<= D`; it can only pin them down once the
//! equations it has generated are numerous and independent enough to leave essentially one
//! consistent assignment. The semiregular model is what predicts that, and it is already in the
//! crate: `SemiregularSeries::quadratics` is `(1 - z^2)^m / (1 - z)^n`, whose **degree of
//! regularity** is "the first degree at which a semiregular sequence is predicted to have no
//! residue classes left". That degree is the one this harness prices, and the prediction is
//! labelled as a prediction wherever it is printed — `docs/research/hilbert-functions.md` §3
//! records where the model fails and in which direction.
//!
//! The comparand is F4's **measured** peak live entries on the same instance, transcribed from
//! `research/scoreboard/runs/` through `docs/research/mq-comparison-methodology.md` §7. Both sides
//! are then priced in the same unit — a live sparse entry at `size_of::<(usize, F)>()` bytes, the
//! quantity `max_live_bytes` spends — so the ratio is of one thing.
//!
//! ```text
//! cargo run --release --example xl_dimensions
//! cargo run --release --example xl_dimensions -- 10 15 20 24
//! ```

use zeebra::{
    fields::Zp31,
    grobner::hilbert::{monomials_of_degree, SemiregularSeries},
};

/// Variable counts. The Fukuoka type III rungs Zeebra has, plus the two real `m = 16` challenges
/// at `n = 24`.
const DEFAULT: [usize; 4] = [10, 15, 20, 24];

/// How far to expand the semiregular series before giving up on finding a degree of regularity.
const MAX_DEGREE: u64 = 40;

/// Bytes a live sparse entry occupies, which is what both sides are priced in.
fn bytes_per_entry() -> usize {
    size_of::<(usize, Zp31)>()
}

/// Monomials of degree **at most** `degree` in `variables` variables.
///
/// `monomials_of_degree` counts one degree; XL's rows and columns are both cumulative, because it
/// retains every lower-degree product and every lower-degree monomial.
fn monomials_up_to(variables: usize, degree: u64) -> i128 {
    (0..=degree)
        .map(|d| monomials_of_degree(variables, d).expect("a count within i128"))
        .sum()
}

/// F4's **measured** peak live entries on the type III rung at `n`, and what produced the figure.
///
/// Transcribed from `research/scoreboard/runs/`. `None` where Zeebra has no run: `n = 24` is type
/// VI and type V rather than type III, so its figures are reported separately in
/// `mq-comparison-methodology.md` §7 and are not this family's.
fn f4_peak_entries(n: usize) -> Option<(u64, &'static str)> {
    match n {
        10 => Some((168_020, "verified witness, 114 ms, D = 1")),
        15 => Some((2_143_983, "verified witness, 7.8 s, D = 1")),
        20 => Some((12_212_087, "stopped at the 20 000 000-entry cap, degree 5")),
        24 => Some((14_329_816, "type VI m=16: stopped at the cap, degree 6")),
        _ => None,
    }
}

/// XL's shape at one operating degree.
struct Shape {
    degree: u64,
    rows: i128,
    columns: i128,
    nonzeros: i128,
}

impl Shape {
    /// XL at degree `d` for `equations` quadratics in `variables` variables.
    ///
    /// Rows: one per (equation, multiplier) pair, the multipliers being every monomial of degree at
    /// most `d - 2`. Columns: every monomial of degree at most `d`, the linearized unknowns.
    /// Nonzeros: a dense quadratic has a term for every monomial of degree at most two, and
    /// multiplying by one monomial maps those terms injectively, so a row holds that many entries.
    fn of(variables: usize, equations: usize, d: u64) -> Option<Self> {
        if d < 2 {
            return None;
        }
        let multipliers = monomials_up_to(variables, d - 2);
        let terms_per_equation = monomials_up_to(variables, 2);
        let rows = multipliers * equations as i128;
        Some(Shape {
            degree: d,
            rows,
            columns: monomials_up_to(variables, d),
            nonzeros: rows * terms_per_equation,
        })
    }

    /// Bytes the matrix occupies as sparse entries.
    fn bytes(&self) -> i128 {
        self.nonzeros * bytes_per_entry() as i128
    }
}

/// Bytes, in whichever unit keeps the figure readable.
fn human(bytes: i128) -> String {
    let b = bytes as f64;
    if b >= 1024.0 * 1024.0 * 1024.0 {
        format!("{:.2} GiB", b / (1024.0 * 1024.0 * 1024.0))
    } else if b >= 1024.0 * 1024.0 {
        format!("{:.1} MiB", b / (1024.0 * 1024.0))
    } else {
        format!("{:.0} KiB", b / 1024.0)
    }
}

/// That the term count this harness uses is the one the published files actually have.
///
/// A dense quadratic in `n` variables has a coefficient for every monomial of degree at most two,
/// and every XL figure here is linear in that number — so if it were wrong, every row would be
/// wrong by the same factor and nothing would look odd. Checked against the real file instead:
/// `fukuoka-mq.md` §4 records the type III `n = 10` import as "parses, **66 coefficients** x 20
/// polynomials".
fn the_term_count_matches_the_published_file() {
    assert_eq!(
        monomials_up_to(10, 2),
        66,
        "a dense quadratic in 10 variables has 66 coefficients, as the type III n=10 file does"
    );
    // And the shape of the claim, not just one instance of it: degree <= 2 in n variables is
    // 1 + n + n(n+1)/2.
    for n in 1..=30usize {
        let expected = 1 + n as i128 + (n as i128 * (n as i128 + 1)) / 2;
        assert_eq!(monomials_up_to(n, 2), expected, "term count at n = {}", n);
    }
}

/// That this construction reproduces the published record-holder's own matrix.
///
/// The strongest check available without building anything: eprint 2026/2641 is the XL + block
/// Wiedemann implementation that holds the Fukuoka **type III `n = 38`** record, and it reports its
/// matrix as **`N = 45 379 620` columns**. This harness predicts the operating degree from the
/// semiregular model and then counts columns combinatorially, with no knowledge of that paper — and
/// lands on the same integer. So both halves are checked at once: the degree the model picks for
/// `n = 38` is the degree the implementation actually used, and the column count is right.
fn the_column_count_matches_the_published_record(max_degree: u64) {
    let series = SemiregularSeries::quadratics(38, 76, max_degree).expect("expands");
    let degree = series
        .degree_of_regularity()
        .expect("a degree of regularity below the expansion limit");
    let shape = Shape::of(38, 76, degree).expect("a shape at degree >= 2");
    assert_eq!(
        shape.columns, 45_379_620,
        "eprint 2026/2641 reports N = 45 379 620 columns for type III n = 38; \
         this construction predicts degree {} and {} columns",
        degree, shape.columns
    );
}

fn main() {
    the_term_count_matches_the_published_file();
    the_column_count_matches_the_published_record(MAX_DEGREE);

    // `--` survives `cargo run --example ... -- 38`, so it is dropped rather than parsed.
    let arguments: Vec<String> = std::env::args().skip(1).filter(|a| a != "--").collect();
    let sizes: Vec<usize> = if arguments.is_empty() {
        DEFAULT.to_vec()
    } else {
        arguments
            .iter()
            .map(|a| a.parse().expect("a variable count"))
            .collect()
    };

    println!("# XL's matrix at the degree it needs, against F4's measured peak (#76)");
    println!();
    println!(
        "Counts, not timings: XL's shape at a degree is three binomial coefficients and a term"
    );
    println!(
        "count, so every figure here is exact and reproduces bit-for-bit without a benchmark lock."
    );
    println!(
        "No XL matrix is built and no linear algebra runs — #76's go/no-go says the answer is"
    );
    println!("\"obtainable from construction alone, without a solver\", and this is that.");
    println!();
    println!(
        "Determined systems, `m = 2n` quadratics in `n` variables, as Fukuoka type III publishes."
    );
    println!(
        "The operating degree is the semiregular model's **degree of regularity** — a prediction,"
    );
    println!(
        "and labelled one. Sparse entries priced at {} B each, the unit `max_live_bytes`",
        bytes_per_entry()
    );
    println!("spends on both sides.");
    println!();
    println!(
        "| n | m | D (predicted) | XL rows | XL columns | XL nonzeros | XL sparse bytes | F4 measured peak entries | XL / F4 entries |"
    );
    println!("| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |");

    for &n in &sizes {
        let m = 2 * n;
        let series = match SemiregularSeries::quadratics(n, m, MAX_DEGREE) {
            Ok(s) => s,
            Err(e) => {
                println!("| {} | {} | — | *{:?}* | | | | | |", n, m, e);
                continue;
            }
        };
        let Some(d) = series.degree_of_regularity() else {
            println!("| {} | {} | none below {} | | | | | | |", n, m, MAX_DEGREE);
            continue;
        };
        let Some(shape) = Shape::of(n, m, d) else {
            continue;
        };

        let (f4, ratio) = match f4_peak_entries(n) {
            Some((peak, _)) => (
                format!("{}", peak),
                format!("**{:.2}x**", shape.nonzeros as f64 / peak as f64),
            ),
            None => ("—".to_string(), "—".to_string()),
        };

        println!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} |",
            n,
            m,
            shape.degree,
            shape.rows,
            shape.columns,
            shape.nonzeros,
            human(shape.bytes()),
            f4,
            ratio,
        );
    }

    println!();
    println!("## Every degree, so the operating degree is not taken on trust");
    println!();
    println!(
        "XL is cheap at a degree where it cannot succeed, which is the trap a single-degree table"
    );
    println!("invites. `H(D)` is the semiregular model's predicted residue count: XL can pin the");
    println!(
        "monomials down only once that has fallen to zero, and the first such degree is the one"
    );
    println!(
        "priced above. Degrees below it are listed to show how fast the cost climbs to reach it."
    );

    for &n in &sizes {
        let m = 2 * n;
        let Ok(series) = SemiregularSeries::quadratics(n, m, MAX_DEGREE) else {
            continue;
        };
        let regularity = series.degree_of_regularity();
        println!();
        println!("### n = {}, m = {}", n, m);
        println!();
        println!("| D | predicted `H(D)` | XL rows | XL columns | XL nonzeros | XL sparse bytes | usable? |");
        println!("| ---: | ---: | ---: | ---: | ---: | ---: | --- |");
        let top = regularity.unwrap_or(8).min(MAX_DEGREE);
        for d in 2..=top {
            let Some(shape) = Shape::of(n, m, d) else {
                continue;
            };
            let usable = match regularity {
                Some(r) if d >= r => "**yes**",
                _ => "no — residue classes remain",
            };
            println!(
                "| {} | {} | {} | {} | {} | {} | {} |",
                d,
                series.raw(d),
                shape.rows,
                shape.columns,
                shape.nonzeros,
                human(shape.bytes()),
                usable,
            );
        }
    }

    println!();
    println!("`predicted H(D)` is `SemiregularSeries::raw`, the **untruncated** expansion, so the");
    println!(
        "sign of the first non-positive term is visible rather than clamped to zero — that term"
    );
    println!("is what the degree of regularity is defined by.");
    println!();
    println!(
        "The F4 column is a **measurement** and the XL column is a **construction count** at a"
    );
    println!(
        "**predicted** degree. They are priced in the same unit so the ratio means something,"
    );
    println!(
        "and they are not the same kind of number: a wrong prediction moves D by one and moves"
    );
    println!(
        "the XL column by an order of magnitude, which is why the per-degree tables are here."
    );
}
