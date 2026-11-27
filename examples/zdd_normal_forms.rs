//! #1168's measurements: the ZDD normal form against the expanded-ANF route on every fixture.
//!
//! cargo run --release --features research-zdd --example zdd_normal_forms -- [--quick] [--out FILE]
//!
//! Each row is one family, size and order (`natural`, or `scrambled-<seed>`, a random topological
//! order) and times both complete routes, the median of 5 runs. The ZDD route verifies the rules,
//! converts the rules and targets ANF→ZDD and normalizes every target; `zdd_out_s` is converting
//! the results back to ANF, timed once and refused on its own past the term budget. The ANF route verifies the rules and substitutes heads into each target.
//! A ladder stops at the first size where either route refuses, or where a run exceeds the wall cap.
//! Then the predeclared go/no-go (#1168 issue comment) is evaluated on the natural-order rows.
//!
//! Development figures: unpinned, from whatever machine runs this.

use std::fs::File;
use std::io::Write;
use std::time::Instant;

use zeebra::boolean::{
    anf::{Anf, AnfWork},
    fixtures::{adder, chi_spn, dense_mq, ladder, Instance},
    normal_form::{anf_normal_form, TriangularRules},
    zdd::{Budget, Zdd},
    ZddError,
};

const TERM_BUDGET: usize = 1 << 21;
const ZDD_BUDGET: Budget = Budget {
    max_nodes: 1 << 23,
    max_cache_entries: 1 << 25,
};
const RUNS: usize = 5;
const SCRAMBLES: u64 = 5;
const WALL_CAP_S: f64 = 30.0;
const PEAK_CAP_BYTES: usize = 256 << 20;

#[derive(Clone, Debug)]
struct ZddRun {
    in_s: f64,
    nf_s: f64,
    /// Converting the results back to ANF: its time and the results, or its refusal.
    out: Result<(f64, Vec<Anf>), ZddError>,
    allocated: usize,
    result_nodes: usize,
    result_terms: u128,
    cache_entries: usize,
    unique_lookups: u64,
    unique_hits: u64,
    cache_lookups: u64,
    cache_hits: u64,
    heap_bytes: usize,
}

#[derive(Clone, Debug, Default)]
struct AnfRun {
    total_s: f64,
    peak_terms: usize,
    products: u64,
    results: Vec<Anf>,
}

fn zdd_route(inst: &Instance, rules: &TriangularRules) -> Result<ZddRun, ZddError> {
    let start = Instant::now();
    let rules = TriangularRules::verify(rules.order().clone(), rules.rules().to_vec())
        .expect("verified once already");
    let mut z = Zdd::with_rules(&rules, ZDD_BUDGET)?;
    let roots: Vec<_> = inst
        .targets
        .iter()
        .map(|t| z.from_anf(t))
        .collect::<Result<_, _>>()?;
    let in_s = start.elapsed().as_secs_f64();
    let nfs: Vec<_> = roots
        .iter()
        .map(|&r| z.normal_form(r))
        .collect::<Result<_, _>>()?;
    let nf_s = start.elapsed().as_secs_f64() - in_s;
    let clock = Instant::now();
    let out = nfs
        .iter()
        .map(|&r| z.to_anf(r, TERM_BUDGET))
        .collect::<Result<Vec<_>, _>>()
        .map(|results| (clock.elapsed().as_secs_f64(), results));
    let stats = z.stats();
    Ok(ZddRun {
        in_s,
        nf_s,
        out,
        allocated: z.allocated_nodes(),
        result_nodes: z.reachable_nodes(&nfs),
        result_terms: nfs.iter().map(|&r| z.term_count(r)).sum(),
        cache_entries: z.cache_entries(),
        unique_lookups: stats.unique_lookups,
        unique_hits: stats.unique_hits,
        cache_lookups: stats.cache_lookups,
        cache_hits: stats.cache_hits,
        heap_bytes: z.heap_bytes(),
    })
}

fn anf_route(inst: &Instance, rules: &TriangularRules) -> Result<AnfRun, ZddError> {
    let start = Instant::now();
    let rules = TriangularRules::verify(rules.order().clone(), rules.rules().to_vec())
        .expect("verified once already");
    let mut work = AnfWork::default();
    let results = inst
        .targets
        .iter()
        .map(|t| anf_normal_form(&rules, t, TERM_BUDGET, &mut work))
        .collect::<Result<_, _>>()?;
    Ok(AnfRun {
        total_s: start.elapsed().as_secs_f64(),
        peak_terms: work.peak_terms,
        products: work.products,
        results,
    })
}

fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(f64::total_cmp);
    xs[xs.len() / 2]
}

/// Runs `route` up to `RUNS` times; the median time replaces the first run's, which is kept.
fn timed<T: Clone>(
    runs: usize,
    mut route: impl FnMut() -> Result<T, ZddError>,
    time: impl Fn(&T) -> f64,
    set: impl Fn(&mut T, f64),
) -> Result<T, ZddError> {
    let first = route()?;
    let mut times = vec![time(&first)];
    for _ in 1..runs {
        times.push(time(&route()?));
    }
    let mut out = first;
    set(&mut out, median(times));
    Ok(out)
}

struct Row {
    family: &'static str,
    size: usize,
    order: String,
    vars: usize,
    zdd: Result<ZddRun, ZddError>,
    anf: Result<AnfRun, ZddError>,
}

impl Row {
    fn zdd_s(&self) -> Option<f64> {
        self.zdd.as_ref().ok().map(|z| z.in_s + z.nf_s)
    }
    fn ratio(&self) -> Option<f64> {
        Some(self.anf.as_ref().ok()?.total_s / self.zdd_s()?)
    }
    fn ratio_out(&self) -> Option<f64> {
        let z = self.zdd.as_ref().ok()?;
        let out_s = z.out.as_ref().ok()?.0;
        Some(self.anf.as_ref().ok()?.total_s / (z.in_s + z.nf_s + out_s))
    }
    fn anf_bytes(&self) -> Option<usize> {
        // A lower bound: one table of the peak size, 32-byte terms plus a control byte.
        self.anf.as_ref().ok().map(|a| a.peak_terms * 33)
    }
}

fn measure(
    family: &'static str,
    size: usize,
    order: String,
    inst: &Instance,
    rules: &TriangularRules,
    runs: usize,
) -> Row {
    let zdd = timed(
        runs,
        || zdd_route(inst, rules),
        |z| z.in_s + z.nf_s,
        |z, t| {
            let scale = t / (z.in_s + z.nf_s);
            z.in_s *= scale;
            z.nf_s *= scale;
        },
    );
    let anf = timed(
        runs,
        || anf_route(inst, rules),
        |a| a.total_s,
        |a, t| a.total_s = t,
    );
    if let (Ok(z), Ok(a)) = (&zdd, &anf) {
        let zdd_results = &z.out.as_ref().expect("the ANF route fit the same budget").1;
        assert_eq!(
            zdd_results, &a.results,
            "{} {order}: the routes disagree",
            inst.name
        );
    }
    Row {
        family,
        size,
        order,
        vars: inst.natural.len(),
        zdd,
        anf,
    }
}

fn csv_header() -> &'static str {
    "family,size,order,vars,zdd_status,zdd_out_status,zdd_in_s,zdd_nf_s,zdd_s,zdd_out_s,allocated_nodes,result_nodes,\
     result_terms,terms_avoided,cache_entries,unique_lookups,unique_hits,cache_lookups,cache_hits,\
     zdd_heap_bytes,anf_status,anf_s,anf_peak_terms,anf_products,anf_bytes_lb,ratio,ratio_out"
}

fn status<T>(r: &Result<T, ZddError>) -> String {
    match r {
        Ok(_) => "ok".into(),
        Err(e) => format!("{e:?}").replace([',', ' '], ""),
    }
}

fn opt<T: std::fmt::Display>(x: Option<T>) -> String {
    x.map(|x| x.to_string()).unwrap_or_default()
}

fn csv_row(r: &Row) -> String {
    let z = r.zdd.as_ref().ok();
    let a = r.anf.as_ref().ok();
    let f = |x: Option<f64>| opt(x.map(|x| format!("{x:.6}")));
    [
        r.family.to_string(),
        r.size.to_string(),
        r.order.clone(),
        r.vars.to_string(),
        status(&r.zdd),
        z.map(|z| status(&z.out)).unwrap_or_default(),
        f(z.map(|z| z.in_s)),
        f(z.map(|z| z.nf_s)),
        f(r.zdd_s()),
        f(z.and_then(|z| z.out.as_ref().ok().map(|o| o.0))),
        opt(z.map(|z| z.allocated)),
        opt(z.map(|z| z.result_nodes)),
        opt(z.map(|z| z.result_terms)),
        opt(z.map(|z| z.result_terms.saturating_sub(z.result_nodes as u128))),
        opt(z.map(|z| z.cache_entries)),
        opt(z.map(|z| z.unique_lookups)),
        opt(z.map(|z| z.unique_hits)),
        opt(z.map(|z| z.cache_lookups)),
        opt(z.map(|z| z.cache_hits)),
        opt(z.map(|z| z.heap_bytes)),
        status(&r.anf),
        f(a.map(|a| a.total_s)),
        opt(a.map(|a| a.peak_terms)),
        opt(a.map(|a| a.products)),
        opt(r.anf_bytes()),
        f(r.ratio()),
        f(r.ratio_out()),
    ]
    .join(",")
}

/// A family, its sizes, and the instances at a size.
type Ladder = (
    &'static str,
    Vec<usize>,
    Box<dyn Fn(usize) -> Vec<Instance>>,
);

/// The ladders, each capped below `MAX_VARS` variables.
fn ladders(quick: bool) -> Vec<Ladder> {
    let up = |from: usize, step: usize, to: usize| (from..=to).step_by(step).collect::<Vec<_>>();
    let cap = |full: usize, small: usize| if quick { small } else { full };
    vec![
        ("adder", up(4, 2, cap(64, 6)), Box::new(|n| vec![adder(n)])),
        (
            "ladder",
            up(4, 2, cap(62, 6)),
            Box::new(|n| vec![ladder(n)]),
        ),
        (
            "chi8",
            up(1, 1, cap(8, 2)),
            Box::new(|r| vec![chi_spn(8, r)]),
        ),
        (
            "mq",
            up(6, 2, cap(64, 6)),
            Box::new(|k| (1..=3).map(|s| dense_mq(k, s)).collect()),
        ),
    ]
}

fn run(quick: bool, out: &mut dyn Write) -> Vec<Row> {
    let runs = if quick { 1 } else { RUNS };
    let mut rows = Vec::new();
    writeln!(out, "{}", csv_header()).unwrap();
    for (family, sizes, build) in ladders(quick) {
        'sizes: for size in sizes {
            for inst in build(size) {
                let mut orders = vec![("natural".to_string(), inst.natural_rules())];
                orders.extend(
                    (1..=SCRAMBLES).map(|s| (format!("scrambled-{s}"), inst.scrambled_rules(s))),
                );
                let mut stop = false;
                for (name, rules) in orders {
                    let row = measure(family, size, name, &inst, &rules, runs);
                    writeln!(out, "{}", csv_row(&row)).unwrap();
                    out.flush().unwrap();
                    let slow = row
                        .zdd_s()
                        .unwrap_or(0.0)
                        .max(row.anf.as_ref().map_or(0.0, |a| a.total_s))
                        > WALL_CAP_S;
                    stop |=
                        row.order == "natural" && (row.zdd.is_err() || row.anf.is_err() || slow);
                    rows.push(row);
                }
                if stop {
                    break 'sizes;
                }
            }
        }
    }
    rows
}

/// The predeclared criterion, evaluated on the natural-order rows of the structured families.
fn verdict(rows: &[Row]) -> String {
    let mut lines = Vec::new();
    let mut passing = 0;
    for family in ["adder", "ladder", "chi8"] {
        let natural: Vec<&Row> = rows
            .iter()
            .filter(|r| r.family == family && r.order == "natural")
            .collect();
        let complete: Vec<&Row> = natural.iter().copied().filter(|r| r.anf.is_ok()).collect();
        let top: Vec<&Row> = complete.iter().rev().take(2).copied().collect();
        let largest = top.first().map_or(0, |r| r.size);
        let refused = natural.iter().any(|r| r.size <= largest && r.zdd.is_err());
        let ok = top.len() == 2
            && !refused
            && top.iter().all(|r| {
                let z = r.zdd.as_ref().unwrap();
                r.ratio().unwrap() >= 10.0
                    && z.heap_bytes <= r.anf_bytes().unwrap()
                    && z.heap_bytes <= PEAK_CAP_BYTES
            });
        passing += ok as usize;
        let scrambled: Vec<f64> = rows
            .iter()
            .filter(|r| r.family == family && r.size == largest && r.order != "natural")
            .filter_map(Row::ratio)
            .collect();
        let detail: Vec<String> = top
            .iter()
            .map(|r| {
                format!(
                    "size {} R={:.2} R_out={:.2} zdd={}B anf>={}B",
                    r.size,
                    r.ratio().unwrap_or(f64::NAN),
                    r.ratio_out().unwrap_or(f64::NAN),
                    r.zdd.as_ref().map_or(0, |z| z.heap_bytes),
                    r.anf_bytes().unwrap_or(0)
                )
            })
            .collect();
        let scrambled_median = if scrambled.is_empty() {
            f64::NAN
        } else {
            median(scrambled)
        };
        lines.push(format!(
            "{family}: {} [{}] scrambled median R at size {largest} = {scrambled_median:.2}",
            if ok { "meets (1)-(2)" } else { "fails" },
            detail.join("; ")
        ));
    }
    lines.push(format!(
        "verdict: {} ({passing} of 3 structured families meet the criterion; GO needs 2)",
        if passing >= 2 { "GO" } else { "NO-GO" }
    ));
    lines.join("\n")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let quick = args.iter().any(|a| a == "--quick");
    let mut out: Box<dyn Write> = match args.iter().position(|a| a == "--out") {
        Some(i) => Box::new(File::create(&args[i + 1]).expect("--out FILE")),
        None => Box::new(std::io::stdout()),
    };
    let rows = run(quick, &mut *out);
    eprintln!("{}", verdict(&rows));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The quick ladder runs every family through both routes, and they agree (`measure` asserts).
    #[test]
    fn the_quick_ladder_runs_and_the_routes_agree() {
        let rows = run(true, &mut std::io::sink());
        assert!(rows.iter().all(|r| r.zdd.is_ok() && r.anf.is_ok()));
        assert!(verdict(&rows).contains("verdict:"));
    }
}
