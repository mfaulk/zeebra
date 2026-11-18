use zeebra::grobner::{ParallelForward, ParallelSymbolic};

/// The symbolic team for a forward arm: no more threads than forward elimination may use, so a
/// w-worker figure runs w threads in both parallel stages (#883, #891). `F4Options::default()`
/// would otherwise leave the team at 16.
pub fn capped_to(forward: ParallelForward) -> ParallelSymbolic {
    match forward {
        ParallelForward::Serial
        | ParallelForward::Auto { max_workers: 1 }
        | ParallelForward::Forced { workers: 1 } => ParallelSymbolic::Serial,
        ParallelForward::Auto { max_workers } => ParallelSymbolic::Auto { max_workers },
        ParallelForward::Forced { workers } => ParallelSymbolic::Auto {
            max_workers: workers,
        },
    }
}
