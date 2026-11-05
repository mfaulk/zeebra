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
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        for line in status.lines() {
            // `VmHWM:   123456 kB`, and the unit is always kB on Linux.
            let value = match line.strip_prefix("VmHWM:") {
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
    use super::peak_resident_bytes;

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

    /// Current resident size, which the peak is a high-water mark of.
    ///
    /// Only the test needs this: the peak is the figure a measurement reports, and the current size
    /// is here to know how far *below* the peak the process is sitting.
    #[cfg(target_os = "linux")]
    fn resident_bytes() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .expect("readable on Linux")
            .lines()
            .find_map(|line| line.strip_prefix("VmRSS:"))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|kb| kb.parse::<u64>().ok())
            .expect("VmRSS is present")
            * 1024
    }

    /// Touching memory raises the reported peak by most of what was touched.
    ///
    /// The property the figure is read for, and the only one asserted: that it responds to real
    /// resident memory. It is deliberately not asserted to stay raised afterwards — see
    /// [`peak_resident_bytes`] on why that does not hold everywhere.
    ///
    /// # Why the ballast is not a constant
    ///
    /// The peak is a **high-water mark**, so touching 32 MB raises it only when the process is
    /// already within 32 MB of its own peak. Under the built-in harness every test shares one
    /// process, so a test that allocated 150 MB and freed it leaves this one 150 MB below the mark
    /// and a fixed 32 MB of ballast cannot move it — which is exactly what happened when M23 added
    /// tests that build 46-variable polynomial systems. The gap is therefore measured and closed
    /// first. Under `cargo nextest`, which CI uses, each test has its own process and the gap is
    /// nearly zero.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_touching_memory_raises_the_peak() {
        const BALLAST: u64 = 32 * 1024 * 1024;

        let before = peak_resident_bytes().expect("readable");
        // Close the distance to the existing high-water mark, then exceed it by the ballast.
        let gap = before.saturating_sub(resident_bytes());
        let ballast_bytes = gap + BALLAST;
        // Written to rather than merely allocated, so the pages are really resident. Every page is
        // touched, which `vec![0u8; _]` alone does not guarantee.
        let mut ballast = vec![0u8; ballast_bytes as usize];
        for slot in ballast.iter_mut().step_by(4096) {
            *slot = 1;
        }
        let during = peak_resident_bytes().expect("readable");

        // Three quarters rather than all of it: the test binary is multi-threaded and the figure
        // is process-wide, so another test's free can land between the two readings.
        assert!(
            during >= before + BALLAST / 4 * 3,
            "{} is not {} bytes above {} (gap to the mark was {})",
            during,
            BALLAST / 4 * 3,
            before,
            gap
        );
        // Kept alive to here so the pages cannot be reclaimed before the reading above.
        drop(ballast);
    }
}
