//! #974 M33-Q thread high-water (plan §11.5, §12.1). One test in its own binary, so the only
//! threads in the process are the harness's, the sampler and the solver's own.

use std::{
    sync::{
        atomic::{AtomicBool, Ordering::Relaxed},
        Arc,
    },
    time::Duration,
};
use zeebra::{
    fields::PrimeFieldElement64,
    grobner::{
        benchmark_systems::katsura, f4_reported, f4_signature_reported, F4Options, ParallelForward,
        ParallelSymbolic, SignatureRoute,
    },
    MonomialOrder,
};

type Wide = PrimeFieldElement64<18446744073709551263>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

fn tasks() -> usize {
    std::fs::read_dir("/proc/self/task").map_or(0, |d| d.count())
}

/// Threads of this process in state `R` (running or runnable), other than `own`. A thread blocked
/// on its team, as the caller is while the shipping F4's workers run, is not computing and is not
/// counted; the signature cascade's caller works beside its `team − 1` helpers and is.
fn running(own: &str) -> usize {
    let Ok(dir) = std::fs::read_dir("/proc/self/task") else {
        return 0;
    };
    dir.flatten()
        .filter(|t| t.file_name().to_str() != Some(own))
        .filter_map(|t| std::fs::read_to_string(t.path().join("stat")).ok())
        .filter(|stat| {
            stat.rsplit_once(") ")
                .is_some_and(|(_, rest)| rest.starts_with('R'))
        })
        .count()
}

/// While `body` runs, sampled every 50 µs: the samples with two or more threads computing, and
/// those with more than `cap`; and how many more threads are alive once it has returned than before.
fn high_water(cap: usize, body: impl FnOnce()) -> (usize, usize, usize) {
    let before = tasks();
    let stop = Arc::new(AtomicBool::new(false));
    let flag = stop.clone();
    let sampler = std::thread::spawn(move || {
        let link = std::fs::read_link("/proc/thread-self").expect("thread-self");
        let own = link
            .file_name()
            .and_then(|n| n.to_str())
            .expect("tid")
            .to_string();
        let (mut parallel, mut over) = (0, 0);
        while !flag.load(Relaxed) {
            let now = running(&own);
            parallel += usize::from(now >= 2);
            over += usize::from(now > cap);
            std::thread::sleep(Duration::from_micros(50));
        }
        (parallel, over)
    });
    body();
    stop.store(true, Relaxed);
    let (parallel, over) = sampler.join().expect("sampler");
    (parallel, over, tasks().saturating_sub(before))
}

fn capped(workers: usize) -> F4Options {
    F4Options {
        max_wall_time: Some(Duration::from_secs(3)),
        parallel_forward: ParallelForward::Auto {
            max_workers: workers,
        },
        parallel_symbolic: ParallelSymbolic::Auto {
            max_workers: workers,
        },
        ..F4Options::default()
    }
}

/// Fails unless a parallel phase was sampled, at most 1% of its samples were over the cap, and no
/// worker outlived the call. A caller spawning or just joining its team is briefly runnable beside
/// it; a team larger than the cap is over it for as long as it computes.
fn check(route: &str, cap: usize, (parallel, over, after): (usize, usize, usize)) {
    eprintln!("{route} cap {cap}: {over} of {parallel} parallel samples over the cap");
    assert!(
        parallel > 0,
        "{route}, cap {cap}: no parallel phase sampled; the cap was not exercised"
    );
    assert!(
        over * 100 <= parallel,
        "{route}, cap {cap}: {over} of {parallel} parallel samples had more than {cap} threads running"
    );
    assert_eq!(after, 0, "{route}, cap {cap}: workers outlived the call");
}

/// On the signature route and the shipping F4 no more threads compute at once than the caller's
/// cap (3 and 16 on Katsura-11, a 3 s slice of it), and no worker outlives the call.
#[test]
fn test_thread_high_water_stays_within_the_worker_cap() {
    let system = katsura::<11, Wide>();
    for cap in [3, 16] {
        let signature = high_water(cap, || {
            let (_, report) = f4_signature_reported(&system, GREVLEX, &capped(cap));
            assert_eq!(report.route, SignatureRoute::Signature);
            assert_eq!(report.workers, cap);
        });
        check("signature route", cap, signature);
        let shipping = high_water(cap, || {
            let _ = f4_reported(&system, GREVLEX, &capped(cap));
        });
        check("shipping F4", cap, shipping);
    }
}
