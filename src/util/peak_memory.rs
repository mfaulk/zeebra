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

    /// Touching 32 MB raises the reported peak by most of 32 MB.
    ///
    /// The property the figure is read for, and the only one asserted: that it responds to real
    /// resident memory. It is deliberately not asserted to stay raised afterwards — see
    /// [`peak_resident_bytes`] on why that does not hold everywhere.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_touching_memory_raises_the_peak() {
        const BALLAST: u64 = 32 * 1024 * 1024;

        let before = peak_resident_bytes().expect("readable");
        // Written to rather than merely allocated, so the pages are really resident. Every page is
        // touched, which `vec![0u8; _]` alone does not guarantee.
        let mut ballast = vec![0u8; BALLAST as usize];
        for slot in ballast.iter_mut().step_by(4096) {
            *slot = 1;
        }
        let during = peak_resident_bytes().expect("readable");

        // Three quarters rather than all of it: the test binary is multi-threaded and the figure
        // is process-wide, so another test's free can land between the two readings.
        assert!(
            during >= before + BALLAST / 4 * 3,
            "{} is not {} bytes above {}",
            during,
            BALLAST / 4 * 3,
            before
        );
        // Kept alive to here so the pages cannot be reclaimed before the reading above.
        drop(ballast);
    }
}
