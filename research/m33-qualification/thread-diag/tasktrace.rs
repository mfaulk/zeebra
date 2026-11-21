// Runs a command and samples /proc/<pid>/task/*/stat from outside it, so the traced process has no
// sampler thread of its own. Output (JSON lines): one `sample` per change of (alive, running set),
// and one `task` per thread with when it was first and last seen and its state counts.
// Build: rustc -O tasktrace.rs. Usage: tasktrace OUT.jsonl -- CMD ARGS...
use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::process::Command;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_path = &args[1];
    assert_eq!(args[2], "--");
    let mut child = Command::new(&args[3]).args(&args[4..]).spawn().expect("spawn");
    let pid = child.id();
    let t0 = Instant::now();
    let dir = format!("/proc/{pid}/task");
    // tid -> (first_us, last_us, states seen as char -> count)
    let mut tasks: BTreeMap<u32, (u128, u128, BTreeMap<char, u64>)> = BTreeMap::new();
    let mut out = fs::File::create(out_path).expect("out");
    let mut last: (usize, Vec<u32>) = (0, Vec::new());
    let mut sweeps: u64 = 0;
    loop {
        sweeps += 1;
        if let Ok(Some(_)) = child.try_wait() {
            break;
        }
        let Ok(rd) = fs::read_dir(&dir) else { break };
        let now = t0.elapsed().as_micros();
        let mut alive = 0;
        let mut running = Vec::new();
        for e in rd.flatten() {
            let Some(tid) = e.file_name().to_str().and_then(|s| s.parse::<u32>().ok()) else {
                continue;
            };
            let Ok(stat) = fs::read_to_string(e.path().join("stat")) else { continue };
            let Some((_, rest)) = stat.rsplit_once(") ") else { continue };
            let state = rest.chars().next().unwrap_or('?');
            alive += 1;
            if state == 'R' {
                running.push(tid);
            }
            let t = tasks.entry(tid).or_insert((now, now, BTreeMap::new()));
            t.1 = now;
            *t.2.entry(state).or_insert(0) += 1;
        }
        running.sort_unstable();
        if (alive, running.clone()) != last {
            writeln!(out, r#"{{"kind":"sample","us":{now},"alive":{alive},"running":{running:?}}}"#)
                .unwrap();
            last = (alive, running);
        }
    }
    let status = child.wait().expect("wait");
    let us = t0.elapsed().as_micros();
    writeln!(out, r#"{{"kind":"sweeps","count":{sweeps},"us":{us}}}"#).unwrap();
    for (tid, (first, last, states)) in &tasks {
        let s: Vec<String> = states.iter().map(|(c, n)| format!(r#""{c}":{n}"#)).collect();
        writeln!(
            out,
            r#"{{"kind":"task","tid":{tid},"first_us":{first},"last_us":{last},"states":{{{}}}}}"#,
            s.join(",")
        )
        .unwrap();
    }
    std::process::exit(status.code().unwrap_or(1));
}
