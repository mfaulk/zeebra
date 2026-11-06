//! The process's peak resident set size, where the platform reports it.
//!
//! Every memory figure elsewhere in this crate is an estimate of what a representation holds:
//! entries counted, multiplied by a byte size. That is the quantity the resource budgets are
//! written in, and it is deliberately not the same thing as the memory the process used. It omits
//! allocator overhead, every temporary, and the peak of whatever computed the input. A measurement
//! that includes all of those is what this provides, so that the two can be reported side by side
//! rather than one being mistaken for the other.

/// The kernel's reported peak resident set size for this process, in bytes, or `None` if
/// unavailable.
///
/// **Process-wide, and not attributable to any one computation.** It covers every allocation the
/// process has made, so it is only informative in a program that does one substantial thing —
/// which is why the callers are example binaries rather than library code.
///
/// **Not reliably monotonic.** `VmHWM` is a high-water mark on mainline Linux, but it is not one
/// everywhere this crate is built: on the kernel these tests run under, freeing 32 MB and reading
/// again returns a *smaller* figure. So treat the value as a ceiling on recent usage rather than
/// as the maximum since the process started, and do not build an argument on a difference between
/// two readings.
///
/// Linux only, from `VmHWM` in `/proc/self/status`. Returns `None` on every other platform and on
/// a Linux where `/proc` is not mounted, rather than guessing.
pub fn peak_resident_bytes() -> Option<u64> {
    status_field_bytes("VmHWM:")
}

/// A `/proc/self/status` size field in bytes, by line prefix, or `None` if unavailable.
#[allow(unused_variables)]
fn status_field_bytes(prefix: &str) -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
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

#[cfg(test)]
mod tests {
    // Every test here is Linux-gated, and so is the import they share.
    #[cfg(target_os = "linux")]
    use super::{peak_resident_bytes, status_field_bytes};

    /// On Linux the peak is reported and is a plausible size for a test process.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_the_peak_is_reported_on_linux() {
        let peak = peak_resident_bytes().expect("/proc/self/status is readable on Linux");
        assert!(
            peak > 256 * 1024,
            "{} bytes is too small to be a process's peak",
            peak
        );
    }

    /// Touching 32 MB raises the reported peak to at least 32 MB above the live RSS beforehand.
    ///
    /// The property the figure is read for, and the only one asserted: that it responds to real
    /// resident memory. It is deliberately not asserted to stay raised afterwards — see
    /// [`peak_resident_bytes`] on why that does not hold everywhere.
    ///
    /// # Why the baseline is `VmRSS` and not the peak
    ///
    /// The peak is a **high-water mark**, so touching 32 MB raises it above the *previous peak*
    /// only when the process is already within 32 MB of that mark. Under the built-in harness
    /// every test shares one process, so a test that allocated 150 MB and freed it leaves this one
    /// 150 MB below the mark and no fixed ballast can move it — which is what broke this test when
    /// M23 added tests that build 46-variable polynomial systems.
    ///
    /// Baselining on live RSS removes that history: after the ballast is resident the live size is
    /// `before + 32 MB`, and the peak is at least the live size, whatever the mark was beforehand.
    /// The alternative is to measure the gap to the mark and allocate `gap + 32 MB`, which this did
    /// briefly; that keeps the peak as the baseline but makes the allocation as large as the
    /// suite's largest freed transient, so it grows with exactly the thing that broke the fixed
    /// ballast. A constant 32 MB is enough here. Under `cargo nextest`, which CI uses, each test
    /// has its own process and the gap is nearly zero either way.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_touching_memory_raises_the_peak() {
        const BALLAST: u64 = 32 * 1024 * 1024;

        let before = status_field_bytes("VmRSS:").expect("readable");
        // Written to rather than merely allocated, so the pages are really resident. Every page is
        // touched, which `vec![0u8; _]` alone does not guarantee.
        let mut ballast = vec![0u8; BALLAST as usize];
        for slot in ballast.iter_mut().step_by(4096) {
            *slot = 1;
        }
        let during = peak_resident_bytes().expect("readable");

        // Three quarters rather than all of it: under the built-in harness the binary is
        // multi-threaded and both figures are process-wide, so another test's free can land
        // between the two readings. Under nextest, a process per test, there is no such thread.
        assert!(
            during >= before + BALLAST / 4 * 3,
            "peak {} is not {} bytes above the {} resident beforehand",
            during,
            BALLAST / 4 * 3,
            before
        );
        // Kept alive to here so the pages cannot be reclaimed before the reading above.
        drop(ballast);
    }
}
