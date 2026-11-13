// Research-only: owned jobs avoid extending borrowed lifetimes across persistent threads.
use std::{
    panic::{catch_unwind, AssertUnwindSafe},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{sync_channel, SyncSender},
        Arc,
    },
    thread::{self, JoinHandle},
};

type Job<S> = Box<dyn FnOnce(&mut S) + Send>;

#[derive(Debug, Eq, PartialEq)]
pub enum Failure {
    Refused,
    Cancelled,
    Panicked,
}

pub struct WorkerPool<S> {
    senders: Vec<SyncSender<Job<S>>>,
    threads: Vec<JoinHandle<()>>,
    max_tasks: usize,
}

impl<S: Default + Send + 'static> WorkerPool<S> {
    pub fn new(workers: usize, max_tasks: usize) -> Result<Self, Failure> {
        if workers == 0 || workers > 128 || max_tasks == 0 {
            return Err(Failure::Refused);
        }
        let mut pool = Self {
            senders: Vec::new(),
            threads: Vec::new(),
            max_tasks,
        };
        for index in 0..workers {
            let (tx, rx) = sync_channel::<Job<S>>(1);
            let worker = thread::Builder::new()
                .name(format!("study-{index}"))
                .spawn(move || {
                    let mut scratch = S::default();
                    while let Ok(job) = rx.recv() {
                        job(&mut scratch);
                    }
                })
                .map_err(|_| Failure::Refused)?;
            pool.senders.push(tx);
            pool.threads.push(worker);
        }
        Ok(pool)
    }

    /// One owner dispatches bounded batches; cancellation is cooperative between jobs.
    pub fn run<T: Send + 'static>(
        &mut self,
        tasks: Vec<impl FnOnce(&mut S) -> T + Send + 'static>,
        cancel: Arc<AtomicBool>,
    ) -> Result<Vec<T>, Failure> {
        if tasks.len() > self.max_tasks {
            return Err(Failure::Refused);
        }
        if cancel.load(Ordering::Acquire) {
            return Err(Failure::Cancelled);
        }
        let count = tasks.len();
        if count == 0 {
            return Ok(Vec::new());
        }
        let (tx, rx) = sync_channel(count);
        for (index, task) in tasks.into_iter().enumerate() {
            let tx = tx.clone();
            let cancel = cancel.clone();
            self.senders[index % self.senders.len()]
                .send(Box::new(move |scratch| {
                    let answer = if cancel.load(Ordering::Acquire) {
                        Err(Failure::Cancelled)
                    } else {
                        catch_unwind(AssertUnwindSafe(|| task(scratch))).map_err(|_| {
                            *scratch = S::default();
                            cancel.store(true, Ordering::Release);
                            Failure::Panicked
                        })
                    };
                    let _ = tx.send((index, answer));
                }))
                .map_err(|_| Failure::Panicked)?;
        }
        drop(tx);
        let mut answers: Vec<Option<T>> = (0..count).map(|_| None).collect();
        let mut error = None;
        for _ in 0..count {
            match rx.recv().map_err(|_| Failure::Panicked)? {
                (index, Ok(answer)) => answers[index] = Some(answer),
                (_, Err(Failure::Panicked)) => error = Some(Failure::Panicked),
                (_, Err(e)) if error.is_none() => error = Some(e),
                _ => {}
            }
        }
        if let Some(error) = error {
            return Err(error);
        }
        if cancel.load(Ordering::Acquire) {
            return Err(Failure::Cancelled);
        }
        Ok(answers.into_iter().map(Option::unwrap).collect())
    }
}

impl<S> Drop for WorkerPool<S> {
    fn drop(&mut self) {
        self.senders.clear();
        for worker in self.threads.drain(..) {
            let _ = worker.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // Repeated batches preserve result order and reuse each worker's scratch allocation.
    #[test]
    fn ordered_batches_reuse_scratch() {
        let mut pool = WorkerPool::<Vec<usize>>::new(2, 4).unwrap();
        for round in 0..4 {
            let answers = pool
                .run(
                    (0..2)
                        .map(|i| {
                            move |s: &mut Vec<usize>| {
                                let before = s.len();
                                s.push(i);
                                (i, before)
                            }
                        })
                        .collect(),
                    Arc::new(AtomicBool::new(false)),
                )
                .unwrap();
            assert_eq!(answers.iter().map(|x| x.0).collect::<Vec<_>>(), vec![0, 1]);
            assert_eq!(answers, vec![(0, round), (1, round)]);
        }
    }

    // Refused or pre-cancelled batches execute no tasks and leave the pool reusable.
    #[test]
    fn refusal_and_cancellation_do_not_execute_tasks() {
        let mut pool = WorkerPool::<()>::new(2, 2).unwrap();
        let count = Arc::new(AtomicUsize::new(0));
        for (size, cancelled, error) in
            [(3, false, Failure::Refused), (2, true, Failure::Cancelled)]
        {
            let tasks = (0..size)
                .map(|_| {
                    let count = count.clone();
                    move |_: &mut ()| {
                        count.fetch_add(1, Ordering::Relaxed);
                    }
                })
                .collect();
            assert_eq!(
                pool.run(tasks, Arc::new(AtomicBool::new(cancelled))),
                Err(error)
            );
        }
        assert_eq!(count.load(Ordering::Relaxed), 0);
        assert_eq!(
            pool.run(vec![|_: &mut ()| 7], Arc::new(AtomicBool::new(false))),
            Ok(vec![7])
        );
    }

    // A task panic is reported after draining the batch and resets contaminated scratch.
    #[test]
    fn panic_does_not_strand_workers() {
        let mut pool = WorkerPool::<Vec<u8>>::new(1, 2).unwrap();
        assert_eq!(
            pool.run(
                vec![|s: &mut Vec<u8>| {
                    s.push(9);
                    panic!("intentional task failure")
                }],
                Arc::new(AtomicBool::new(false))
            ),
            Err(Failure::Panicked)
        );
        assert_eq!(
            pool.run(
                vec![|s: &mut Vec<u8>| s.len()],
                Arc::new(AtomicBool::new(false))
            ),
            Ok(vec![0])
        );
    }

    // Cancellation from a running job drains queued work before allowing another batch.
    #[test]
    fn cancellation_during_dispatch_is_reusable() {
        let mut pool = WorkerPool::<()>::new(1, 3).unwrap();
        let cancel = Arc::new(AtomicBool::new(false));
        let token = cancel.clone();
        let count = Arc::new(AtomicUsize::new(0));
        let tasks: Vec<Job<()>> = (0..3)
            .map(|_| {
                let count = count.clone();
                let token = token.clone();
                Box::new(move |_: &mut ()| {
                    count.fetch_add(1, Ordering::Relaxed);
                    token.store(true, Ordering::Release);
                }) as Job<()>
            })
            .collect();
        assert_eq!(pool.run(tasks, cancel), Err(Failure::Cancelled));
        assert_eq!(count.load(Ordering::Relaxed), 1);
        assert_eq!(
            pool.run(vec![|_: &mut ()| 9], Arc::new(AtomicBool::new(false))),
            Ok(vec![9])
        );
    }

    // Zero worker counts and empty batches are handled without spawning unusable pools.
    #[test]
    fn empty_and_invalid_batches() {
        assert!(matches!(WorkerPool::<()>::new(0, 2), Err(Failure::Refused)));
        let mut pool = WorkerPool::<()>::new(2, 2).unwrap();
        let tasks: Vec<fn(&mut ())> = Vec::new();
        assert_eq!(
            pool.run(tasks, Arc::new(AtomicBool::new(false))),
            Ok(Vec::new())
        );
    }
}
