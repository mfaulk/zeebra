//! Spawning a team of scoped worker threads that is joined before its call returns (#1002).
//!
//! `std::thread::scope` waits for each closure to return, not for its thread to exit: a handle
//! the scope joins implicitly is detached, and its OS thread may still be tearing down, or waiting
//! for a CPU to do so, while the caller starts the next team. Every team spawns through [`spawn`]
//! and joins each handle with [`join`] or its own `handle.join()`, which waits for the thread to
//! exit, so a worker cap holds at every instant rather than only per team.

use std::thread::{Scope, ScopedJoinHandle};

/// [`Scope::spawn`], counted by the test-only census when the calling thread has one armed.
pub(crate) fn spawn<'scope, T, F>(
    scope: &'scope Scope<'scope, '_>,
    f: F,
) -> ScopedJoinHandle<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    #[cfg(test)]
    let f = census::enlist(f);
    scope.spawn(f)
}

/// Wait for `handle`'s thread to exit and return its value, resuming its panic if it had one.
pub(crate) fn join<T>(handle: ScopedJoinHandle<'_, T>) -> T {
    handle
        .join()
        .unwrap_or_else(|payload| std::panic::resume_unwind(payload))
}

/// Runs `work(0..workers)` as one team whose first member is the calling thread, and returns
/// each member's outcome in index order. Only `workers - 1` threads are spawned and each is joined
/// before this returns, so at most `workers` threads compute at any instant: a caller that spawned
/// a full team and then blocked in `join` would be runnable beside all of it while spawning. A
/// panic in any member, the caller's included, is returned as that member's `Err`. A team of zero
/// runs nothing.
pub(crate) fn run<T: Send>(
    workers: usize,
    work: impl Fn(usize) -> T + Sync,
) -> Vec<std::thread::Result<T>> {
    if workers == 0 {
        return Vec::new();
    }
    let work = &work;
    std::thread::scope(|scope| {
        let members: Vec<_> = (1..workers)
            .map(|index| spawn(scope, move || work(index)))
            .collect();
        let mut outcomes = Vec::with_capacity(workers);
        outcomes.push(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || work(0),
        )));
        outcomes.extend(members.into_iter().map(ScopedJoinHandle::join));
        outcomes
    })
}

/// [`join`] on every handle, in order.
pub(crate) fn join_all<'scope, T>(
    handles: impl IntoIterator<Item = ScopedJoinHandle<'scope, T>>,
) -> Vec<T> {
    handles.into_iter().map(join).collect()
}

/// Live worker threads spawned from one test thread, counted until each thread exits.
#[cfg(test)]
pub(crate) mod census {
    use std::{
        cell::RefCell,
        sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        },
        time::Duration,
    };

    struct Shared {
        live: AtomicUsize,
        peak: AtomicUsize,
        spawned: AtomicUsize,
        linger: Duration,
    }

    thread_local! {
        static ARMED: RefCell<Option<Arc<Shared>>> = const { RefCell::new(None) };
        static MEMBER: RefCell<Option<Member>> = const { RefCell::new(None) };
    }

    /// Dropped with the worker thread's locals, after its closure has returned.
    struct Member(Arc<Shared>);

    impl Drop for Member {
        fn drop(&mut self) {
            std::thread::sleep(self.0.linger);
            self.0.live.fetch_sub(1, Ordering::SeqCst);
        }
    }

    /// Counts the threads [`super::spawn`] starts from this thread while it is alive. Each one
    /// stays live for `linger` after its closure returns, which widens the window in which an
    /// unjoined thread overlaps the next team.
    pub(crate) struct Census {
        shared: Arc<Shared>,
        previous: Option<Arc<Shared>>,
    }

    impl Census {
        pub(crate) fn arm(linger: Duration) -> Self {
            let shared = Arc::new(Shared {
                live: AtomicUsize::new(0),
                peak: AtomicUsize::new(0),
                spawned: AtomicUsize::new(0),
                linger,
            });
            let previous = ARMED.replace(Some(shared.clone()));
            Census { shared, previous }
        }

        /// Most threads alive at once.
        pub(crate) fn peak(&self) -> usize {
            self.shared.peak.load(Ordering::SeqCst)
        }

        /// Threads not yet exited.
        pub(crate) fn live(&self) -> usize {
            self.shared.live.load(Ordering::SeqCst)
        }

        /// Threads spawned.
        pub(crate) fn spawned(&self) -> usize {
            self.shared.spawned.load(Ordering::SeqCst)
        }
    }

    impl Drop for Census {
        fn drop(&mut self) {
            ARMED.set(self.previous.take());
        }
    }

    pub(super) fn enlist<T, F: FnOnce() -> T + Send>(f: F) -> impl FnOnce() -> T + Send {
        let shared = ARMED.with_borrow(Clone::clone);
        if let Some(shared) = &shared {
            let live = shared.live.fetch_add(1, Ordering::SeqCst) + 1;
            shared.peak.fetch_max(live, Ordering::SeqCst);
            shared.spawned.fetch_add(1, Ordering::SeqCst);
        }
        move || {
            if let Some(shared) = shared {
                MEMBER.set(Some(Member(shared)));
            }
            f()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{census::Census, *};
    use std::time::Duration;

    const LINGER: Duration = Duration::from_millis(50);

    fn team(workers: usize, joined: bool) {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers).map(|i| spawn(scope, move || i)).collect();
            if joined {
                assert_eq!(join_all(handles), (0..workers).collect::<Vec<_>>());
            }
        });
    }

    #[test]
    fn joined_teams_never_overlap() {
        let census = Census::arm(LINGER);
        for _ in 0..3 {
            team(4, true);
            assert_eq!(census.live(), 0);
        }
        assert_eq!(census.spawned(), 12);
        assert_eq!(census.peak(), 4);
    }

    /// The failure this module exists for: the scope's implicit join returns before its threads
    /// exit, so the next team starts beside them.
    #[test]
    fn unjoined_teams_outlive_their_scope() {
        let census = Census::arm(LINGER);
        team(4, false);
        team(4, false);
        assert!(census.peak() > 4, "peak {}", census.peak());
    }

    /// A team of `n` spawns `n - 1` threads, runs member 0 on the caller, and keeps index order.
    #[test]
    fn run_counts_the_caller_as_a_member() {
        let census = Census::arm(LINGER);
        let caller = std::thread::current().id();
        let outcomes = run(4, |i| (i, std::thread::current().id() == caller));
        let values: Vec<_> = outcomes.into_iter().map(Result::unwrap).collect();
        assert_eq!(values, vec![(0, true), (1, false), (2, false), (3, false)]);
        assert_eq!(census.spawned(), 3);
        assert_eq!(census.live(), 0);
    }

    /// An empty team runs no member, not even on the caller.
    #[test]
    fn run_of_zero_workers_runs_nothing() {
        let outcomes = run(0, |_| -> usize { unreachable!("no member") });
        assert!(outcomes.is_empty());
    }

    /// A panic in any member, the caller's own included, comes back as that member's error.
    #[test]
    fn run_returns_each_members_panic() {
        let outcomes = run(3, |i| {
            if i != 1 {
                panic!("member {i}");
            }
            i
        });
        assert!(outcomes[0].is_err());
        assert_eq!(*outcomes[1].as_ref().unwrap(), 1);
        assert!(outcomes[2].is_err());
    }

    #[test]
    fn join_resumes_a_worker_panic() {
        let caught = std::panic::catch_unwind(|| {
            std::thread::scope(|scope| join(spawn(scope, || panic!("worker"))))
        });
        let payload = caught.expect_err("the panic propagates");
        assert_eq!(payload.downcast_ref::<&str>(), Some(&"worker"));
    }
}
