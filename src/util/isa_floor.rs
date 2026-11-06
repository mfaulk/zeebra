//! Which vector instruction set this artifact was compiled for, as a string a measurement can print.
//!
//! This exists because a figure taken without the ISA floor is not comparable with one taken with
//! it, and nothing made the difference visible. `.cargo/config.toml` sets
//! `-C target-cpu=x86-64-v3` under `target.'cfg(target_arch = "x86_64")'`, and the `RUSTFLAGS`
//! environment variable **replaces** that rather than adding to it — so any shell that sets
//! `RUSTFLAGS` for an unrelated reason, including setting it to the empty string, silently builds
//! at the baseline x86-64 level with no AVX2.
//!
//! `docs/MILESTONE-SIMD-PARALLELISM.md` §3.1 recorded that trap after it nearly shipped a silent
//! CI regression, and the config file warns about it in a comment. It then cost #185 a crossover
//! constant measured in the wrong state and #231 a whole set of figures, because the commands that
//! produced them set `RUSTFLAGS`. Neither was detectable from the output. The fix that generalizes
//! is not a sharper reading of the warning; it is for every measurement to print the state it was
//! taken in, so a figure and its ISA travel together.
//!
//! Why this is not an assertion. A `#[test]` that required AVX2 would fail for any consumer
//! building this crate as a dependency, since `.cargo/config.toml` applies only when cargo runs in
//! this directory and is explicitly not inherited downstream. The repository-local check belongs in
//! `tools/vec_census.sh`, which inspects a built artifact; this function is for making the state
//! legible wherever a number is reported.

/// The vector instruction set the current artifact was compiled for, for a measurement header.
///
/// `"x86-64-v3 or better (AVX2)"` when the floor is present, `"baseline x86-64 (NO AVX2 — \
/// RUSTFLAGS probably displaced the ISA floor)"` when it is not, and the architecture's name on a
/// target where the question does not arise.
///
/// Compile-time, through `cfg!(target_feature = ..)`, which is exactly what `-C target-cpu` sets —
/// so this reports what the compiler was told rather than what the CPU can do. That is the right
/// quantity: a figure's comparability depends on how it was built, not on where it ran.
pub fn isa_floor() -> &'static str {
    if cfg!(not(target_arch = "x86_64")) {
        return "not x86_64; the x86-64-v3 floor does not apply";
    }
    if cfg!(target_feature = "avx512f") {
        "x86-64-v4 or better (AVX-512)"
    } else if cfg!(target_feature = "avx2") {
        "x86-64-v3 or better (AVX2)"
    } else if cfg!(target_feature = "avx") {
        "AVX but not AVX2 — below the x86-64-v3 floor this repository configures"
    } else {
        "baseline x86-64, NO AVX2 — RUSTFLAGS probably displaced the ISA floor; \
         see tools/vec_census.sh"
    }
}

/// Whether the artifact has the AVX2 floor the repository's build configuration asks for.
///
/// For a measurement harness that wants to refuse to record a figure rather than merely label it.
/// Always true on a non-x86_64 target, where the floor is not the relevant question.
pub fn has_isa_floor() -> bool {
    cfg!(not(target_arch = "x86_64")) || cfg!(target_feature = "avx2")
}

#[cfg(test)]
mod tests {
    use super::{has_isa_floor, isa_floor};

    /// The two functions agree: the floor is reported present exactly when `has_isa_floor` says so.
    #[test]
    fn test_the_description_agrees_with_the_predicate() {
        let described = isa_floor();
        let reported_absent = described.contains("NO AVX2") || described.contains("below the");
        assert_eq!(
            has_isa_floor(),
            !reported_absent,
            "the description {:?} disagrees with has_isa_floor()",
            described
        );
    }

    /// The description names an ISA level rather than being empty, so a header line is never blank.
    ///
    /// Deliberately not asserting *which* level: that would fail for a consumer building this crate
    /// without this repository's `.cargo/config.toml`, which is every consumer. See the module
    /// comment.
    #[test]
    fn test_the_description_is_not_empty() {
        assert!(!isa_floor().is_empty());
    }
}
