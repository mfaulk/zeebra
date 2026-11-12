//! Running one external solver process under declared limits, and measuring what it cost.
//!
//! # Why an external process's peak RSS is not [`crate::util::peak_resident_bytes`]
//!
//! [`crate::util::peak_resident_bytes`] reads `VmHWM` from `/proc/self/status`: the *harness's*
//! high-water mark. An external solver runs in a different address space, so its footprint never
//! appears there at all. The measurement has to come from the child.
//!
//! # The wrapper hazard, which has already cost this project a figure wrong by 7000x
//!
//! `/proc/<pid>/status` is per-process, so a reading is only the solver's if the pid is the
//! solver's. Two common wrappers break that:
//!
//! * **`timeout` forks.** `timeout 600 msolve ...` makes `timeout` the direct child and `msolve`
//!   its child. `timeout`'s own `VmHWM` is a couple of megabytes, so a naive read of the direct
//!   child reports ~2 MB for a run that used gigabytes.
//! * **`taskset` execs.** `taskset -c 0 msolve ...` replaces itself with `msolve`, keeping the
//!   pid — so this one is *safe*, but only by accident of `taskset`'s implementation, and
//!   `taskset -c 0 timeout 600 msolve` is not.
//! * **`sh -c "..."`** may fork or exec depending on the command, so it is never safe to assume.
//!
//! The contract's resolution is structural rather than a warning: [`Supervisor`] spawns the solver
//! binary **directly** and implements the time limit itself, so the direct child always *is* the
//! solver. CPU affinity is inherited across `fork` and preserved across `exec`, so pinning belongs
//! on the harness process (`taskset -c ... cargo run ...`, which is what `ZEEBRA_AFFINITY` already
//! records) and not on each child. Where a tool genuinely cannot be invoked without a forking
//! wrapper — a launcher script, say — [`RssPolicy::ProcessTree`] is the escape hatch, and it marks
//! its own figures as sampled rather than exact.
//!
//! # What is exact and what is sampled
//!
//! `VmHWM` is maintained by the kernel, so the *direct child's* peak is exact — subject only to
//! being read before the process exits, since `/proc/<pid>` disappears at reap. The supervisor
//! therefore polls while the child runs and reports the last successful reading. A tree figure is
//! the maximum over polls of the summed `VmRSS` of the child and its descendants, which is
//! genuinely sampled: it can miss a spike shorter than the poll interval, and it double-counts
//! pages shared between the processes. [`RssBasis`] travels with every measurement so that a
//! recorded number says which of these it is.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    fmt::{Display, Formatter},
    fs::File,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

/// `USER_HZ`, the unit of the CPU-time fields in `/proc/<pid>/stat`.
///
/// Fixed at 100 by Linux's `/proc` ABI on every architecture this crate is built for, independent
/// of the kernel's internal `CONFIG_HZ`; `sysconf(_SC_CLK_TCK)` returns the same 100. Named as a
/// constant rather than called through `libc` because the core crate takes no new dependency for
/// it. Override with `ZEEBRA_CLK_TCK` if a platform ever disagrees.
const DEFAULT_USER_HZ: u64 = 100;

/// How the peak resident set size in a [`ProcessMeasurement`] was obtained.
///
/// Recorded alongside the figure because the two available methods are not the same kind of
/// quantity, and a resource *bound* must never be read as a resource *measurement*.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RssBasis {
    /// `VmHWM` of the supervisor's direct child, polled from `/proc/<pid>/status`.
    ///
    /// Each reading is exact at its observation time. A process may exit between polls, so the
    /// last reading can miss a late peak, especially for a short-lived child.
    DirectChildHighWater,

    /// The child reads its own kernel `VmHWM` after computation and serialization preparation.
    /// Covers that phase even when the process finishes between supervisor polls; final exit
    /// and stdout-transfer allocations occur after this snapshot.
    ChildSelfHighWater,

    /// The maximum over polls of the summed `VmRSS` of the direct child and every descendant.
    ///
    /// **Sampled and an over-count.** A spike shorter than `interval` is missed, and pages shared
    /// between the processes are counted once per process. Use only where a forking wrapper cannot
    /// be avoided.
    ProcessTreeSampled { interval: Duration, samples: u64 },

    /// Peak bytes **allocated**, from a tracking allocator inside the measured process.
    ///
    /// **Not resident memory, and not comparable with either variant above.** A reservation the
    /// process never writes to is counted here and is absent from `VmHWM`, and the gap is not
    /// slack spread thinly: on the Fukuoka III `n = 20` row (#237) F4's pair queue reached 2^28
    /// slots in a **single** 20 480 MiB allocation of which about 60% was never written, giving
    /// 21 674 MB allocated against 13 996 MB resident. One allocation larger than the whole
    /// resident peak is why no amount of care in reading "peak memory" distinguishes the two
    /// quantities — only recording which one it is does.
    ///
    /// Available only for Zeebra's own rows, since it needs a `#[global_allocator]` in the
    /// measured process. No external solver can report it.
    AllocatorTracked,

    /// `VmHWM` of the **harness's own** process, for an in-crate engine that runs in it.
    ///
    /// The same quantity as [`Self::DirectChildHighWater`] — a kernel-maintained high-water mark
    /// for one process — and comparable with it, but with a weaker attribution: a subprocess
    /// figure covers the one solve the supervisor spawned, while this one covers everything the
    /// harness process has done. So it is only reported when the caller declares that the process
    /// is doing one row and nothing else.
    SelfHighWater,

    /// No figure: not Linux, `/proc` unreadable, measurement disabled, or the child exited before
    /// the first poll.
    Unavailable,
}

impl Display for RssBasis {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DirectChildHighWater => write!(f, "direct-child VmHWM (exact)"),
            Self::ChildSelfHighWater => {
                write!(f, "child-self VmHWM after serialization (kernel snapshot)")
            }
            Self::ProcessTreeSampled { interval, samples } => write!(
                f,
                "process-tree VmRSS sampled every {:?} over {} polls (lower bound)",
                interval, samples
            ),
            Self::AllocatorTracked => {
                write!(
                    f,
                    "peak bytes allocated by a tracking allocator (not resident)"
                )
            }
            Self::SelfHighWater => write!(f, "harness-process VmHWM (exact, one row per process)"),
            Self::Unavailable => write!(f, "unavailable"),
        }
    }
}

/// How the CPU time in a [`ProcessMeasurement`] was obtained.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CpuBasis {
    /// `utime + stime` from `/proc/<pid>/stat`, converted at `user_hz` ticks per second.
    ///
    /// Polled like the RSS figure, so it is the last reading before exit and can undercount the
    /// final poll interval. Covers the child only, not its descendants.
    ProcStatTicks { user_hz: u64 },

    /// No figure available.
    Unavailable,
}

/// Which processes the supervisor should measure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RssPolicy {
    /// Poll the direct child's `VmHWM`. The default, and exact — see the module documentation.
    DirectChild,

    /// Poll the direct child and every descendant, summing `VmRSS`.
    ///
    /// Only for a tool that cannot be spawned without a forking wrapper. Costs a scan of `/proc`
    /// per poll and yields a sampled figure.
    ProcessTree,

    /// Take no memory measurement.
    None,
}

/// What one supervised process cost, and whether a limit stopped it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProcessMeasurement {
    /// Wall-clock time from just before `spawn` to the reap, including the kill on a timeout.
    pub wall: Duration,

    /// The child's CPU time, if `/proc` gave one.
    pub cpu: Option<Duration>,

    /// How `cpu` was obtained.
    pub cpu_basis: CpuBasis,

    /// The child's peak resident set size in bytes, if a figure was obtained.
    pub peak_rss_bytes: Option<u64>,

    /// How `peak_rss_bytes` was obtained. Read this before comparing two figures.
    pub rss_basis: RssBasis,

    /// The child's exit code, or `None` if it was killed or died on a signal.
    pub exit_code: Option<i32>,

    /// True if the wall-clock limit expired and the supervisor killed the child.
    ///
    /// **Not a failure of the solver and not a speed result.** A timed-out run has a wall time
    /// equal to the limit and says nothing about how much longer it needed.
    pub timed_out: bool,

    /// True when a sampled RSS reading crossed the requested ceiling and the child was killed.
    pub memory_limited: bool,
}

impl ProcessMeasurement {
    /// True if the child exited 0 and was not killed.
    pub fn succeeded(&self) -> bool {
        !self.timed_out && !self.memory_limited && self.exit_code == Some(0)
    }
}

/// Why a supervised process could not be run or reaped.
///
/// Distinct from the child *failing*: a non-zero exit is reported through
/// [`ProcessMeasurement::exit_code`], not here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpawnError {
    /// The binary could not be started: absent, not executable, or not on the path given.
    ///
    /// This is the **missing tool** case every adapter must report rather than treat as slow.
    Unavailable { binary: String, reason: String },

    /// The supervisor's **own** filesystem or process work failed: the scratch directory, the
    /// output file the child's streams are redirected to, or waiting on the child.
    ///
    /// Named for the side that failed rather than for the syscall, because nothing here is ever the
    /// tool's doing — the tool has not started yet, or has not been reaped. An adapter must turn
    /// this into [`RunFailure::Harness`](super::RunFailure::Harness), which a board counts as a
    /// skipped row (#610).
    Harness { detail: String },
}

impl Display for SpawnError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable { binary, reason } => write!(f, "cannot run {}: {}", binary, reason),
            Self::Harness { detail } => write!(f, "{}", detail),
        }
    }
}

impl std::error::Error for SpawnError {}

impl From<std::io::Error> for SpawnError {
    fn from(e: std::io::Error) -> Self {
        Self::Harness {
            detail: e.to_string(),
        }
    }
}

/// A definite verdict that `binary` cannot be started, reached without starting anything.
///
/// The absent-tool path must not be able to lose a race with anything else: this resolution
/// consults no clock, spawns no process and writes no file, so neither a wall-clock budget nor
/// scratch I/O can come between "the tool is not installed" and the report that says so (#391).
///
/// Asymmetric on purpose. `Some` is returned only where **no** file exists at any name the OS
/// would try. Anything that might still start — a file that exists but may not be executable, a
/// `PATH` this code cannot reconstruct — yields `None` and falls through to the spawn, which
/// reports the kernel's own reason. A false `Some` would turn an installed tool into a skipped
/// measurement, so the asymmetry runs in the direction that cannot corrupt a sweep.
pub fn unavailable_binary(binary: &str) -> Option<SpawnError> {
    let absent = |reason: &str| {
        Some(SpawnError::Unavailable {
            binary: binary.to_string(),
            reason: reason.to_string(),
        })
    };
    if binary.is_empty() {
        return absent("no binary was named");
    }
    if binary.contains('/') {
        // A name with a separator is used as given: the OS searches for it no more than this does.
        if Path::new(binary).is_file() {
            return None;
        }
        return absent("no such file");
    }
    // A bare name is searched for along `PATH`. With `PATH` unset the kernel applies a default
    // this code declines to guess, so the spawn decides that case instead.
    let search = std::env::var_os("PATH")?;
    for directory in std::env::split_paths(&search) {
        // POSIX reads an empty component as the current directory, and so does `execvp`.
        let directory = if directory.as_os_str().is_empty() {
            PathBuf::from(".")
        } else {
            directory
        };
        if directory.join(binary).is_file() {
            return None;
        }
    }
    absent("not found on PATH")
}

/// One invocation: a binary, its arguments, and where its output goes.
///
/// Deliberately not a [`Command`]: an adapter describes the invocation and the supervisor owns the
/// spawning, so no adapter can reintroduce the wrapper hazard or forget the stdin redirect.
#[derive(Clone, Debug)]
pub struct Invocation {
    /// The solver binary. Spawned directly — see the module documentation on wrappers.
    pub binary: String,

    /// Arguments, already split. No shell is involved, so nothing is word-split or globbed.
    pub arguments: Vec<OsString>,

    /// Working directory for the child. Also where relative paths in `arguments` resolve.
    pub work_dir: PathBuf,

    /// File that receives both stdout and stderr.
    ///
    /// A file and not a pipe: a child whose pipe fills while the parent is waiting blocks forever,
    /// which is exactly the case a time limit exists for and exactly the case a pipe deadlocks in.
    pub output_path: PathBuf,

    /// Environment variables to set for the child, on top of the inherited environment.
    pub environment: Vec<(String, String)>,
}

impl Invocation {
    /// An invocation of `binary` in `work_dir`, writing output to `output_path`.
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<PathBuf>,
        output_path: impl Into<PathBuf>,
    ) -> Self {
        Self {
            binary: binary.into(),
            arguments: Vec::new(),
            work_dir: work_dir.into(),
            output_path: output_path.into(),
            environment: Vec::new(),
        }
    }

    /// Append one argument.
    pub fn arg(mut self, argument: impl Into<OsString>) -> Self {
        self.arguments.push(argument.into());
        self
    }

    /// Append several arguments.
    pub fn args<I, S>(mut self, arguments: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<OsString>,
    {
        self.arguments.extend(arguments.into_iter().map(Into::into));
        self
    }

    /// Set one environment variable for the child.
    pub fn env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.environment.push((key.into(), value.into()));
        self
    }

    /// A definite verdict that this invocation cannot start, reached without starting it.
    ///
    /// [`unavailable_binary`] with one extra abstention: an invocation that sets `PATH` for the
    /// child is searched along *that* `PATH`, so a lookup along this process's would be answering
    /// a different question and the spawn is left to decide.
    pub fn unavailable(&self) -> Option<SpawnError> {
        if self.environment.iter().any(|(key, _)| key == "PATH") {
            return None;
        }
        unavailable_binary(&self.binary)
    }

    /// The command line as a single shell-quoted string, for the reproduction field of a record.
    ///
    /// Quoting is the conservative kind: anything outside a safe set is single-quoted. It is for a
    /// human to paste, and it is not parsed back.
    pub fn command_line(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (key, value) in &self.environment {
            parts.push(format!("{}={}", key, shell_quote(value)));
        }
        parts.push(shell_quote(&self.binary));
        for argument in &self.arguments {
            parts.push(shell_quote(&argument.to_string_lossy()));
        }
        parts.join(" ")
    }
}

/// `word` if it needs no quoting, else `'word'` with embedded quotes escaped.
fn shell_quote(word: &str) -> String {
    let safe = !word.is_empty()
        && word
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_=+./:,@%^".contains(c));
    if safe {
        return word.to_string();
    }
    format!("'{}'", word.replace('\'', r#"'\''"#))
}

/// Spawns one external process at a time under a wall-clock limit, and measures it.
#[derive(Clone, Debug)]
pub struct Supervisor {
    max_rss_bytes: Option<u64>,
    wall_limit: Duration,
    poll_interval: Duration,
    rss_policy: RssPolicy,
}

impl Supervisor {
    /// A supervisor with a wall-clock limit, polling every 10 ms, measuring the direct child.
    pub fn new(wall_limit: Duration) -> Self {
        Self {
            wall_limit,
            max_rss_bytes: None,
            poll_interval: Duration::from_millis(10),
            rss_policy: RssPolicy::DirectChild,
        }
    }

    /// Enforce a sampled RSS ceiling, killing and reaping the direct child on crossing.
    /// Requires readable process RSS; the ceiling can be exceeded between poll ticks.
    pub fn with_max_rss_bytes(mut self, limit: Option<u64>) -> Self {
        self.max_rss_bytes = limit;
        self
    }

    /// Change the poll interval.
    ///
    /// Shorter polling tightens the sampled figures and the timeout's overshoot, at one or more
    /// `/proc` reads per poll. The timeout itself is checked on the same tick, so the interval is
    /// also the granularity of the kill.
    pub fn with_poll_interval(mut self, interval: Duration) -> Self {
        self.poll_interval = interval.max(Duration::from_micros(100));
        self
    }

    /// Change which processes are measured.
    pub fn with_rss_policy(mut self, policy: RssPolicy) -> Self {
        self.rss_policy = policy;
        self
    }

    /// The wall-clock limit this supervisor enforces.
    pub fn wall_limit(&self) -> Duration {
        self.wall_limit
    }

    /// Run `invocation` to completion, to the limit, or to a spawn failure.
    ///
    /// A definitely-absent binary ([`unavailable_binary`]) is reported before anything is created,
    /// so the verdict depends on neither the wall limit nor the filesystem. Otherwise the output
    /// file is created (and truncated) by this call, and on return it holds whatever the child
    /// wrote, including on a timeout — a partial log is evidence and is not discarded.
    ///
    /// # Errors
    /// [`SpawnError::Unavailable`] if the binary could not be started, which is the case an
    /// adapter must turn into a skipped-and-reported run rather than a failure of the solver.
    /// [`SpawnError::Harness`] if the supervisor's own work — the scratch directory, the output
    /// file, reaping the child — failed. Never the tool's doing, and never the tool's row.
    pub fn run(&self, invocation: &Invocation) -> Result<ProcessMeasurement, SpawnError> {
        if let Some(absent) = invocation.unavailable() {
            return Err(absent);
        }
        std::fs::create_dir_all(&invocation.work_dir)?;
        let output_file = File::create(&invocation.output_path)?;
        let error_file = output_file.try_clone()?;

        let mut command = Command::new(&invocation.binary);
        command
            .args(&invocation.arguments)
            .current_dir(&invocation.work_dir)
            // Null, not inherited: a solver that reads a prompt from a terminal would otherwise
            // hang until the limit, and the limit is not supposed to be the normal exit path.
            .stdin(Stdio::null())
            .stdout(Stdio::from(output_file))
            .stderr(Stdio::from(error_file));
        for (key, value) in &invocation.environment {
            command.env(key, value);
        }

        let started = Instant::now();
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(e) => {
                return Err(SpawnError::Unavailable {
                    binary: invocation.binary.clone(),
                    reason: e.to_string(),
                })
            }
        };
        let pid = child.id();

        let mut watcher = Watcher::new(pid, self.rss_policy, self.poll_interval);
        let deadline = started + self.wall_limit;
        let mut timed_out = false;
        let mut memory_limited = false;
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break Some(status),
                Ok(None) => {}
                Err(e) => {
                    return Err(SpawnError::Harness {
                        detail: e.to_string(),
                    })
                }
            }
            // Sampled before the deadline check so that a run which times out still carries the
            // readings taken while it was alive.
            watcher.poll();
            if let Some(limit) = self.max_rss_bytes {
                match watcher.rss().0 {
                    Some(peak) if peak > limit => {
                        let _ = child.kill();
                        let _ = child.wait();
                        memory_limited = true;
                        break None;
                    }
                    None => {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(SpawnError::Harness {
                            detail: "cannot enforce RSS cap without a process RSS reading".into(),
                        });
                    }
                    _ => {}
                }
            }
            if Instant::now() >= deadline {
                // Killed and reaped. Leaving it would accumulate one zombie per timeout across a
                // sweep, and an unreaped child keeps its output file open.
                let _ = child.kill();
                let _ = child.wait();
                timed_out = true;
                break None;
            }
            std::thread::sleep(self.poll_interval);
        };

        let wall = started.elapsed();
        let (peak_rss_bytes, rss_basis) = watcher.rss();
        let (cpu, cpu_basis) = watcher.cpu();

        Ok(ProcessMeasurement {
            wall,
            cpu,
            cpu_basis,
            peak_rss_bytes,
            rss_basis,
            exit_code: status.and_then(|status| status.code()),
            timed_out,
            memory_limited,
        })
    }
}

/// Accumulates `/proc` readings for one running child.
struct Watcher {
    pid: u32,
    policy: RssPolicy,
    interval: Duration,
    samples: u64,
    /// Best `VmHWM` seen for the direct child.
    direct_high_water: Option<u64>,
    /// Best summed tree `VmRSS` seen.
    tree_peak: Option<u64>,
    /// Whether any descendant was ever observed, which is what makes a tree figure necessary.
    saw_descendants: bool,
    /// Last `utime + stime` in ticks.
    cpu_ticks: Option<u64>,
}

impl Watcher {
    fn new(pid: u32, policy: RssPolicy, interval: Duration) -> Self {
        Self {
            pid,
            policy,
            interval,
            samples: 0,
            direct_high_water: None,
            tree_peak: None,
            saw_descendants: false,
            cpu_ticks: None,
        }
    }

    /// Take one reading. Silently does nothing where `/proc` is unavailable.
    fn poll(&mut self) {
        if matches!(self.policy, RssPolicy::None) {
            // CPU time is still worth having, and costs one read.
            self.poll_cpu();
            return;
        }
        self.samples += 1;
        self.poll_cpu();

        if let Some(hwm) = status_field_bytes(self.pid, "VmHWM:") {
            self.direct_high_water = Some(self.direct_high_water.unwrap_or(0).max(hwm));
        }

        if matches!(self.policy, RssPolicy::ProcessTree) {
            let tree = descendants_including(self.pid);
            if tree.len() > 1 {
                self.saw_descendants = true;
            }
            let summed: u64 = tree
                .iter()
                .filter_map(|pid| status_field_bytes(*pid, "VmRSS:"))
                .sum();
            if summed > 0 {
                self.tree_peak = Some(self.tree_peak.unwrap_or(0).max(summed));
            }
        }
    }

    fn poll_cpu(&mut self) {
        if let Some(ticks) = cpu_ticks(self.pid) {
            // Monotonic in the kernel, so `max` only guards against a torn read.
            self.cpu_ticks = Some(self.cpu_ticks.unwrap_or(0).max(ticks));
        }
    }

    /// The peak RSS figure and the basis that describes it.
    fn rss(&self) -> (Option<u64>, RssBasis) {
        // `AllocatorTracked` and `SelfHighWater` are deliberately unreachable here: both come from
        // inside a process, and nothing this supervisor observes from outside produces either.
        match self.policy {
            RssPolicy::None => (None, RssBasis::Unavailable),
            RssPolicy::DirectChild => match self.direct_high_water {
                Some(bytes) => (Some(bytes), RssBasis::DirectChildHighWater),
                None => (None, RssBasis::Unavailable),
            },
            RssPolicy::ProcessTree => {
                // With no descendant ever seen the exact figure is available and is the better
                // one, so the basis says so rather than claiming a sample.
                if !self.saw_descendants {
                    if let Some(bytes) = self.direct_high_water {
                        return (Some(bytes), RssBasis::DirectChildHighWater);
                    }
                }
                let peak = match (self.tree_peak, self.direct_high_water) {
                    (Some(tree), Some(direct)) => Some(tree.max(direct)),
                    (Some(tree), None) => Some(tree),
                    (None, direct) => direct,
                };
                match peak {
                    Some(bytes) => (
                        Some(bytes),
                        RssBasis::ProcessTreeSampled {
                            interval: self.interval,
                            samples: self.samples,
                        },
                    ),
                    None => (None, RssBasis::Unavailable),
                }
            }
        }
    }

    /// The CPU figure and its basis.
    fn cpu(&self) -> (Option<Duration>, CpuBasis) {
        let user_hz = user_hz();
        match self.cpu_ticks {
            Some(ticks) => (
                Some(Duration::from_nanos(
                    ticks.saturating_mul(1_000_000_000) / user_hz.max(1),
                )),
                CpuBasis::ProcStatTicks { user_hz },
            ),
            None => (None, CpuBasis::Unavailable),
        }
    }
}

/// `USER_HZ`, from `ZEEBRA_CLK_TCK` if it is set to a positive integer.
fn user_hz() -> u64 {
    std::env::var("ZEEBRA_CLK_TCK")
        .ok()
        .and_then(|value| value.trim().parse::<u64>().ok())
        .filter(|hz| *hz > 0)
        .unwrap_or(DEFAULT_USER_HZ)
}

/// A size field from another process's `/proc/<pid>/status`, in bytes.
///
/// `None` once the process has been reaped, which is why the supervisor polls while it runs rather
/// than reading once at the end.
#[allow(unused_variables)]
fn status_field_bytes(pid: u32, prefix: &str) -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string(format!("/proc/{}/status", pid)).ok()?;
        for line in status.lines() {
            // `VmHWM:   123456 kB`, and the unit is always kB on Linux.
            let value = match line.strip_prefix(prefix) {
                Some(value) => value,
                None => continue,
            };
            let kilobytes: u64 = value
                .split_whitespace()
                .next()
                .and_then(|number| number.parse().ok())?;
            return Some(kilobytes * 1024);
        }
        None
    }

    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// `utime + stime` in `USER_HZ` ticks from `/proc/<pid>/stat`.
#[allow(unused_variables)]
fn cpu_ticks(pid: u32) -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let stat = std::fs::read_to_string(format!("/proc/{}/stat", pid)).ok()?;
        let fields = stat_fields(&stat)?;
        // Fields are 1-indexed in proc(5): 14 is utime and 15 is stime. `stat_fields` returns
        // field 3 onwards, so utime is index 11.
        let utime: u64 = fields.get(11)?.parse().ok()?;
        let stime: u64 = fields.get(12)?.parse().ok()?;
        Some(utime + stime)
    }

    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

/// The whitespace-separated fields of a `/proc/<pid>/stat` line from field 3 (`state`) onwards.
///
/// Field 2 is the executable name in parentheses and **may itself contain spaces and
/// parentheses**, so the line cannot simply be split: everything up to the *last* `)` is dropped.
/// A tool launched through a shell script easily has a space in `comm`, so this is not theoretical.
fn stat_fields(stat: &str) -> Option<Vec<&str>> {
    let tail = &stat[stat.rfind(')')? + 1..];
    Some(tail.split_whitespace().collect())
}

/// `pid` and every descendant of it, from one scan of `/proc`.
///
/// A snapshot: a process that forks and exits between two polls is invisible to both. That is the
/// sampling weakness [`RssBasis::ProcessTreeSampled`] exists to declare.
#[allow(unused_variables)]
fn descendants_including(pid: u32) -> Vec<u32> {
    #[cfg(target_os = "linux")]
    {
        let mut children: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
        let entries = match std::fs::read_dir("/proc") {
            Ok(entries) => entries,
            Err(_) => return vec![pid],
        };
        for entry in entries.flatten() {
            let name = entry.file_name();
            let candidate: u32 = match name.to_string_lossy().parse() {
                Ok(candidate) => candidate,
                Err(_) => continue,
            };
            let stat = match std::fs::read_to_string(format!("/proc/{}/stat", candidate)) {
                Ok(stat) => stat,
                // Exited between the readdir and the read. Normal, and not an error.
                Err(_) => continue,
            };
            let fields = match stat_fields(&stat) {
                Some(fields) => fields,
                None => continue,
            };
            // Field 4 is ppid, so index 1 of the tail.
            if let Some(parent) = fields.get(1).and_then(|p| p.parse::<u32>().ok()) {
                children.entry(parent).or_default().push(candidate);
            }
        }

        let mut tree = vec![pid];
        let mut frontier = vec![pid];
        while let Some(next) = frontier.pop() {
            for child in children.get(&next).into_iter().flatten() {
                // Guards against a pid-reuse cycle rather than against a real process tree.
                if !tree.contains(child) {
                    tree.push(*child);
                    frontier.push(*child);
                }
            }
        }
        tree
    }

    #[cfg(not(target_os = "linux"))]
    {
        vec![pid]
    }
}

/// Read a run's output file, or the empty string if it cannot be read.
///
/// The empty string and not an error: a timed-out or crashed run may have produced nothing, and
/// "no output" is a parse failure the adapter should report in its own vocabulary rather than an
/// I/O failure of the harness.
pub fn read_output(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::{
        descendants_including, read_output, shell_quote, stat_fields, unavailable_binary,
        Invocation, RssBasis, RssPolicy, SpawnError, Supervisor,
    };
    use std::time::Duration;

    /// A scratch directory unique to the calling test.
    fn scratch(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "zeebra-supervisor-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).expect("a writable scratch directory");
        dir
    }

    /// A missing binary is reported as `Unavailable` naming the binary, not as a failed run.
    ///
    /// The skipped-and-reported path every adapter depends on: a tool that is not installed must
    /// be distinguishable from a tool that ran and lost.
    #[test]
    fn test_a_missing_binary_is_unavailable_and_not_a_slow_run() {
        let dir = scratch("missing");
        let invocation = Invocation::new(
            "zeebra-no-such-solver-binary",
            &dir,
            dir.join("missing.out"),
        );
        let outcome = Supervisor::new(Duration::from_secs(5)).run(&invocation);
        match outcome {
            Err(SpawnError::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-solver-binary");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An absent binary is resolved under a zero budget and without creating any file, so neither
    /// the clock nor the filesystem can stand between absence and the report of it.
    #[test]
    fn test_an_absent_binary_is_resolved_before_the_clock_and_before_any_file() {
        // Deliberately not `scratch`, which would create the directory this asserts nothing
        // creates.
        let dir = std::env::temp_dir().join(format!(
            "zeebra-supervisor-absent-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let output = dir.join("absent.out");
        let invocation = Invocation::new("zeebra-no-such-solver-binary", &dir, &output);
        // A budget nothing can meet: were the verdict ever clock-coupled again, this would fail
        // every time rather than once under suite load (#391).
        let outcome = Supervisor::new(Duration::ZERO).run(&invocation);
        match outcome {
            Err(SpawnError::Unavailable { binary, .. }) => {
                assert_eq!(binary, "zeebra-no-such-solver-binary");
            }
            other => panic!("expected Unavailable, got {:?}", other),
        }
        assert!(!dir.exists(), "{} was created", dir.display());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Definite absence is reported by path lookup, and anything that might still start is left
    /// for the spawn to judge.
    #[test]
    fn test_absence_is_resolved_by_path_lookup_and_only_when_definite() {
        assert!(unavailable_binary("zeebra-no-such-solver-binary").is_some());
        assert!(unavailable_binary("").is_some());
        assert!(unavailable_binary("/no/such/directory/zeebra-solver").is_some());

        // The test binary's own path exists, so it is not this function's to refuse.
        let own = std::env::current_exe().expect("the test binary's own path");
        assert!(unavailable_binary(&own.to_string_lossy()).is_none());

        // A file that exists but may not be executable is the spawn's call: the kernel's reason is
        // better than a guess, and a false refusal would skip an installed tool.
        let dir = scratch("maybe-executable");
        let file = dir.join("maybe-executable");
        std::fs::write(&file, b"not a program").expect("a writable scratch file");
        assert!(unavailable_binary(&file.to_string_lossy()).is_none());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// An invocation that sets `PATH` for the child abstains from the parent-side lookup, so a
    /// tool reachable only along the child's own `PATH` is never pre-emptively called absent.
    #[test]
    fn test_an_invocation_that_sets_path_defers_to_the_spawn() {
        let dir = std::env::temp_dir().join("zeebra-supervisor-child-path");
        let plain = Invocation::new("zeebra-no-such-solver-binary", &dir, dir.join("x.out"));
        assert!(plain.unavailable().is_some());
        assert!(plain.env("PATH", "/nowhere").unavailable().is_none());
    }

    /// A bare name that `PATH` resolves is not refused, which is the branch a present tool takes.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_a_bare_name_found_on_path_is_not_refused() {
        // The same `/bin/sh` the measured-run tests here already depend on, reached as a bare name
        // so that the `PATH` walk itself is covered.
        assert!(unavailable_binary("sh").is_none());
    }

    /// A process that exits 0 is measured as succeeded, with its output captured to the file.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_a_successful_run_is_measured_and_its_output_captured() {
        let dir = scratch("ok");
        let output = dir.join("ok.out");
        let invocation = Invocation::new("/bin/echo", &dir, &output).arg("@done");
        let measurement = Supervisor::new(Duration::from_secs(10))
            .run(&invocation)
            .expect("/bin/echo is runnable");
        assert!(measurement.succeeded(), "{:?}", measurement);
        assert!(!measurement.timed_out);
        assert_eq!(measurement.exit_code, Some(0));
        assert_eq!(read_output(&output).trim(), "@done");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A non-zero exit is carried as an exit code, not as a spawn error.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_a_nonzero_exit_is_an_exit_code_and_not_a_spawn_error() {
        let dir = scratch("fail");
        let invocation = Invocation::new("/bin/sh", &dir, dir.join("fail.out"))
            .arg("-c")
            .arg("exit 3");
        let measurement = Supervisor::new(Duration::from_secs(10))
            .run(&invocation)
            .expect("/bin/sh is runnable");
        assert_eq!(measurement.exit_code, Some(3));
        assert!(!measurement.succeeded());
        let _ = std::fs::remove_dir_all(&dir);
    }

    // A direct child crossing its RSS cap is killed and reported as a memory stop.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_an_rss_limit_kills_the_child() {
        let dir = scratch("rss-limit");
        let invocation = Invocation::new("/bin/sleep", &dir, dir.join("out")).arg("30");
        let result = Supervisor::new(Duration::from_secs(10))
            .with_max_rss_bytes(Some(1))
            .run(&invocation)
            .unwrap();
        assert!(result.memory_limited);
        assert!(!result.timed_out);
        assert!(!result.succeeded());
        assert!(result.peak_rss_bytes.unwrap() > 1);
        let _ = std::fs::remove_dir_all(dir);
    }

    /// A run that outlives its limit is killed, flagged `timed_out`, and has no exit code.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_a_run_past_its_limit_is_killed_and_flagged() {
        let dir = scratch("timeout");
        let invocation = Invocation::new("/bin/sleep", &dir, dir.join("timeout.out")).arg("30");
        let measurement = Supervisor::new(Duration::from_millis(150))
            .with_poll_interval(Duration::from_millis(5))
            .run(&invocation)
            .expect("/bin/sleep is runnable");
        assert!(measurement.timed_out, "{:?}", measurement);
        assert_eq!(measurement.exit_code, None);
        assert!(!measurement.succeeded());
        // The limit is checked on a poll tick, so overshoot is bounded by the interval plus the
        // kill, and a generous ceiling is all this can assert on a shared machine.
        assert!(
            measurement.wall < Duration::from_secs(10),
            "{:?} is not a prompt kill",
            measurement.wall
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A child that touches memory is measured on the exact basis, at roughly the size it touched.
    ///
    /// The claim the contract rests on: the figure is the *child's* footprint and not the
    /// harness's. 48 MB is asked for and 24 MB asserted, leaving room for the allocator.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_a_childs_peak_rss_is_measured_on_the_exact_basis() {
        let dir = scratch("rss");
        // `yes` is not portable enough and `dd` writes; a shell loop building a large variable is
        // available wherever /bin/sh is, and `sleep` holds it resident across several polls.
        let invocation = Invocation::new("/bin/sh", &dir, dir.join("rss.out"))
            .arg("-c")
            .arg("s=x; i=0; while [ $i -lt 23 ]; do s=\"$s$s\"; i=$((i+1)); done; sleep 1");
        let measurement = Supervisor::new(Duration::from_secs(30))
            .with_poll_interval(Duration::from_millis(5))
            .run(&invocation)
            .expect("/bin/sh is runnable");
        assert_eq!(measurement.rss_basis, RssBasis::DirectChildHighWater);
        let peak = measurement
            .peak_rss_bytes
            .expect("a child alive for a second is polled");
        assert!(
            peak > 8 * 1024 * 1024,
            "{} bytes is too small for a child holding ~8 MB of shell variable",
            peak
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// With no descendant observed, the tree policy still reports the exact direct-child basis.
    ///
    /// Sampling is a cost, so it is only paid when there is something to sample.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_the_tree_policy_reports_the_exact_basis_when_nothing_forked() {
        let dir = scratch("tree-single");
        let invocation = Invocation::new("/bin/sleep", &dir, dir.join("tree.out")).arg("0.3");
        let measurement = Supervisor::new(Duration::from_secs(10))
            .with_poll_interval(Duration::from_millis(5))
            .with_rss_policy(RssPolicy::ProcessTree)
            .run(&invocation)
            .expect("/bin/sleep is runnable");
        assert_eq!(measurement.rss_basis, RssBasis::DirectChildHighWater);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Disabling the memory policy yields no figure and says so, rather than yielding zero.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_no_policy_yields_no_figure_rather_than_zero() {
        let dir = scratch("none");
        let invocation = Invocation::new("/bin/echo", &dir, dir.join("none.out")).arg("hi");
        let measurement = Supervisor::new(Duration::from_secs(10))
            .with_rss_policy(RssPolicy::None)
            .run(&invocation)
            .expect("/bin/echo is runnable");
        assert_eq!(measurement.peak_rss_bytes, None);
        assert_eq!(measurement.rss_basis, RssBasis::Unavailable);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The tree of this process includes this process.
    #[test]
    fn test_a_process_tree_includes_its_root() {
        let tree = descendants_including(std::process::id());
        assert_eq!(tree.first(), Some(&std::process::id()));
    }

    /// `/proc/<pid>/stat` fields are read past a `comm` containing spaces and parentheses.
    ///
    /// The field split has to drop everything up to the *last* `)`, not the first.
    #[test]
    fn test_stat_fields_survive_a_parenthesised_command_name() {
        let stat = "1234 (my (odd) name) S 42 1234 1234 0 -1 0 0 0 0 0 7 11 0 0";
        let fields = stat_fields(stat).expect("a closing parenthesis");
        assert_eq!(fields[0], "S", "field 3 is the state");
        assert_eq!(fields[1], "42", "field 4 is the ppid");
        assert_eq!(fields[11], "7", "field 14 is utime");
        assert_eq!(fields[12], "11", "field 15 is stime");
    }

    /// A reproduction command line quotes only what needs it, and carries the environment.
    #[test]
    fn test_a_command_line_is_quoted_for_a_human_to_paste() {
        let invocation = Invocation::new("msolve", "/tmp/w", "/tmp/w/out")
            .arg("-f")
            .arg("katsura-8.ms")
            .arg("a b")
            .env("OMP_NUM_THREADS", "1");
        assert_eq!(
            invocation.command_line(),
            "OMP_NUM_THREADS=1 msolve -f katsura-8.ms 'a b'"
        );
    }

    /// Quoting escapes an embedded single quote rather than producing unbalanced text.
    #[test]
    fn test_quoting_escapes_an_embedded_single_quote() {
        assert_eq!(shell_quote("it's"), r#"'it'\''s'"#);
        assert_eq!(shell_quote(""), "''");
        assert_eq!(shell_quote("plain-1.0/x"), "plain-1.0/x");
    }

    /// An unreadable output path reads as the empty string rather than panicking.
    #[test]
    fn test_a_missing_output_file_reads_as_empty() {
        assert_eq!(read_output(std::path::Path::new("/nonexistent/zeebra")), "");
    }
}
