//! Driving external Gröbner engines as subprocesses, under declared limits, with measured cost.
//!
//! # What this is for
//!
//! Zeebra's cryptanalysis scoreboard answers "can this cipher be broken, and at what cost". This
//! module answers a different question — "how does Zeebra's F4 compare with msolve, Groebner.jl,
//! Sagebrush and Singular on the same ideal" — and the two have different failure modes, so they
//! have different types. The distinction that organizes everything here is the one between
//! **cannot** and **slower**: a tool that will not accept a 64-bit prime field has not lost a
//! race, and the single most common way a cross-library benchmark becomes false is by quoting a
//! ratio against a comparand that could not represent the input.
//!
//! The protocol this implements is `docs/research/external-comparison-protocol.md`; the corpus is
//! `docs/research/cross-library-corpus.md`; the board the rows land in is `research/competitive/`.
//!
//! # Layout
//!
//! * [`contract`] — `ExternalSolver` and the vocabulary every adapter speaks: `Task`,
//!   `Instance`, `Limits`, `RunStatus`, `Measurement`, `Invariants`. **Start here if you are
//!   writing an adapter.**
//! * [`process`] — [`Supervisor`], which spawns one solver under a
//!   wall-clock limit and measures its wall time, CPU time and peak RSS. Also the home of the
//!   reasoning about *whose* peak RSS a `/proc` reading is, which is the subtlest thing in this
//!   module.
//! * [`board`] — [`CompetitiveBoard`] and its record: the durable schema and the generated
//!   Markdown renderer the rows land in. Lives at `research/competitive/`, deliberately apart
//!   from the cryptanalysis scoreboard.
//! * [`corpus`] — the cross-library ladder, and the two naming hazards that produce a different
//!   ideal without producing an error: Katsura's off-by-one indexing and affine-versus-homogenized
//!   Cyclic. Both resolved against another engine's own distributed input files.
//! * [`singular`] — the reference adapter, over the Singular installation the differential
//!   harness already drives. Read it as the worked example.
//!
//! # Licensing
//!
//! msolve, Groebner.jl and Singular are GPL; Sagebrush is MIT OR Apache-2.0. Running a GPL binary
//! as a separate process places no obligation on Zeebra's MIT core, and that is the only thing
//! this module does with them — it writes an input file, spawns a process, and parses text. No
//! GPL source is reused. See `docs/research/external-provenance-policy.md`.
//!
//! # Feature gate
//!
//! [`contract`] and [`singular`] sit behind `external-runners`, on by default and adding **no
//! dependency**: everything here is `std`, because the interface to every one of these tools is
//! text. The gate exists so that an adapter which does need a dependency can be added behind a
//! sub-feature without the core crate acquiring it, and so that a consumer who wants none of this
//! can switch it off.
//!
//! [`process`] is **not** gated, because the differential oracle now runs through it: process
//! supervision stopped being optional the moment there was one implementation of it instead of
//! two.

#[cfg(feature = "external-runners")]
pub mod board;
#[cfg(feature = "external-runners")]
pub mod contract;
#[cfg(feature = "external-runners")]
pub mod corpus;
#[cfg(feature = "external-runners")]
pub mod msolve;
pub mod process;
#[cfg(feature = "external-runners")]
pub mod singular;

#[cfg(feature = "external-runners")]
pub use board::{
    BoardError, CompetitiveBoard, CompetitiveRecord, Outcome, Speedup, COMPETITIVE_HISTORY_CONTRACT,
};
#[cfg(feature = "external-runners")]
pub use contract::{
    order_from_tag, order_tag, Answer, Disagreement, ExternalSolver, FieldSpec, Instance,
    Invariants, LimitStop, Limits, Measurement, NotComparable, RunFailure, RunReport, RunStatus,
    Support, Task, ToolVersion, Unsupported, Verification,
};
#[cfg(feature = "external-runners")]
pub use corpus::{cyclic_instance, katsura_instance, CorpusEntry, Rung, REFERENCE_CHARACTERISTIC};
pub use process::{
    read_output, CpuBasis, Invocation, ProcessMeasurement, RssBasis, RssPolicy, SpawnError,
    Supervisor,
};
#[cfg(feature = "external-runners")]
pub use singular::SingularSolver;
