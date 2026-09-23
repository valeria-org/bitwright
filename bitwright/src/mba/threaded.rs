//! A hard deadline around any solver.

use std::sync::Arc;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::time::Duration;

use super::expr::MbaExpr;
use super::solve::{MbaAnswer, MbaBudget, MbaSolver};

/// Runs each question on its own thread and waits at most `timeout`: an answer that is late is
/// abandoned and reported as [`MbaAnswer::Exhausted`] (never cached, so a later call may try
/// again). While `max_abandoned` abandoned questions are still running, new ones are refused
/// as exhausted, which bounds the threads left behind. The only threads are the ones this
/// instance starts; nothing is global.
///
/// A deadline makes answers depend on timing; the engine treats an exhausted answer as not
/// final, so a memoized result never depends on it. A panic inside the solver is answered as
/// unsupported. The cap is checked before a question starts, so concurrent callers may briefly
/// exceed it by their number.
pub struct ThreadedSolver<S> {
    inner: Arc<S>,
    timeout: Duration,
    max_abandoned: usize,
    abandoned: Arc<AtomicUsize>,
    id: String,
}

impl<S: MbaSolver + 'static> ThreadedSolver<S> {
    /// Wraps `inner` with a deadline.
    pub fn new(inner: S, timeout: Duration, max_abandoned: usize) -> Self {
        let id = inner.id().to_string();
        ThreadedSolver {
            inner: Arc::new(inner),
            timeout,
            max_abandoned,
            abandoned: Arc::new(AtomicUsize::new(0)),
            id,
        }
    }

    /// Questions abandoned and still running.
    pub fn abandoned(&self) -> usize {
        self.abandoned.load(Ordering::Acquire)
    }
}

impl<S> core::fmt::Debug for ThreadedSolver<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ThreadedSolver")
            .field("id", &self.id)
            .field("timeout", &self.timeout)
            .field("max_abandoned", &self.max_abandoned)
            .finish_non_exhaustive()
    }
}

impl<S: MbaSolver + 'static> MbaSolver for ThreadedSolver<S> {
    fn id(&self) -> &str {
        // The deadline does not change answers that arrive, so the inner id keys the caches.
        &self.id
    }

    fn polynomial_fragments(&self) -> bool {
        self.inner.polynomial_fragments()
    }

    fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer {
        const RUNNING: u8 = 0;
        const DONE: u8 = 1;
        const ABANDONED: u8 = 2;
        if self.abandoned.load(Ordering::Acquire) >= self.max_abandoned {
            return MbaAnswer::Exhausted;
        }
        let (tx, rx) = mpsc::channel();
        let (inner, p, budget) = (self.inner.clone(), p.clone(), *budget);
        let abandoned = self.abandoned.clone();
        // One state per question, decided once: whoever moves it out of RUNNING first wins.
        let state = Arc::new(AtomicU8::new(RUNNING));
        let st = state.clone();
        let spawned = std::thread::Builder::new()
            .name("bitwright-mba".into())
            .spawn(move || {
                // A panic in the solver is an answer, not a lost question.
                let answer = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    inner.solve(&p, &budget)
                }))
                .unwrap_or_else(|_| MbaAnswer::Unsupported("the solver panicked".into()));
                let _ = tx.send(answer);
                if st
                    .compare_exchange(RUNNING, DONE, Ordering::AcqRel, Ordering::Acquire)
                    .is_err()
                {
                    // The caller gave up on it and counted it: uncount.
                    abandoned.fetch_sub(1, Ordering::AcqRel);
                }
            });
        if spawned.is_err() {
            return MbaAnswer::Exhausted;
        }
        match rx.recv_timeout(self.timeout) {
            Ok(a) => a,
            Err(_) => {
                // Count it first, so that the worker's uncount can never precede it.
                self.abandoned.fetch_add(1, Ordering::AcqRel);
                if state
                    .compare_exchange(RUNNING, ABANDONED, Ordering::AcqRel, Ordering::Acquire)
                    .is_ok()
                {
                    MbaAnswer::Exhausted
                } else {
                    // The worker finished (and sent) just in time.
                    self.abandoned.fetch_sub(1, Ordering::AcqRel);
                    rx.recv().unwrap_or(MbaAnswer::Exhausted)
                }
            }
        }
    }
}
