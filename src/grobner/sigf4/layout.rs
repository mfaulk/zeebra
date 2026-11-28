//! #1078 (M35 WP D): the four row layouts of the serial cascade's batch rows, and a census of what
//! each batch's live account holds under every one of them, computed exactly from entry counts.
//! Only the batch's own rows change between arms: materialised new pivots stay owned `(u32, F)`,
//! as do the pivot maps and the workspaces.
//!
//! - **Source-backed:** a reducer multiple keeps only its column handles and reads coefficients from
//!   its basis element, which the basis already holds. Targets stay owned.
//! - **u16:** every batch row is split into `u16` columns and `F` coefficients (a `(u16, F)` tuple is
//!   no smaller than `(u32, F)` once `F` is 4 or 8 bytes). Batches wider than [`U16_COLUMNS`] keep
//!   the baseline layout.

/// The widest batch whose column indices fit `u16`: 0 through 65,535.
pub const U16_COLUMNS: usize = 1 << 16;

/// Arms in factorial order.
pub const ARMS: [&str; 4] = ["baseline", "source", "u16", "both"];

/// [`super::SigF4Options::row_layout`]: the layout a batch's rows are built in. Applied only to the
/// serial cascade at one worker without a lane; any other batch keeps [`RowLayout::Baseline`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RowLayout {
    /// Owned `(u32, F)` entries.
    #[default]
    Baseline,
    /// Reducer multiples as `u32` columns, coefficients read from their basis element.
    Source,
    /// Every batch row as `u16` columns beside `F` coefficients, in batches of at most
    /// [`U16_COLUMNS`] columns.
    U16,
    /// [`RowLayout::Source`] and [`RowLayout::U16`] together.
    Both,
}

impl RowLayout {
    /// The arm's index in [`ARMS`].
    pub fn index(self) -> usize {
        self as usize
    }

    /// Whether reducer multiples borrow their coefficients.
    pub fn source(self) -> bool {
        matches!(self, Self::Source | Self::Both)
    }

    /// Whether narrow batches use `u16` columns.
    pub fn narrow(self) -> bool {
        matches!(self, Self::U16 | Self::Both)
    }

    /// Parses an [`ARMS`] name.
    pub fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "baseline" => Self::Baseline,
            "source" => Self::Source,
            "u16" => Self::U16,
            "both" => Self::Both,
            _ => return None,
        })
    }
}

/// One batch's row bytes under each arm, in [`ARMS`] order.
pub fn row_bytes(
    target_entries: usize,
    reducer_entries: usize,
    columns: usize,
    coefficient: usize,
    entry: usize,
) -> [usize; 4] {
    let narrow = columns <= U16_COLUMNS;
    let (index, split) = if narrow {
        (2, 2 + coefficient)
    } else {
        (4, entry)
    };
    [
        (target_entries + reducer_entries) * entry,
        target_entries * entry + reducer_entries * 4,
        (target_entries + reducer_entries) * split,
        target_entries * split + reducer_entries * index,
    ]
}

/// Per-arm maxima over the run's batches.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LayoutCensus {
    /// Largest live account of any batch, per arm.
    pub peak_live_bytes: [usize; 4],
    /// Batch row bytes summed over the run, per arm.
    pub row_bytes: [usize; 4],
    /// Coefficient bytes copied into reducer rows, which the source-backed arms do not copy.
    pub reducer_coefficient_bytes: usize,
    pub batches: usize,
    /// Batches too wide for `u16` indices.
    pub wide_batches: usize,
    /// Batches built in a layout other than the baseline.
    pub layout_batches: usize,
}

impl LayoutCensus {
    /// Records one batch: `rows` is [`row_bytes`] for it, `rest` the up-front charge besides the
    /// rows, `variable` what was charged after it (the reduced rows), and `built` whether the batch
    /// was built in a non-baseline layout.
    pub fn record(
        &mut self,
        rows: [usize; 4],
        rest: usize,
        variable: usize,
        columns: usize,
        reducer_coefficient_bytes: usize,
        built: bool,
    ) {
        for (arm, bytes) in rows.iter().enumerate() {
            self.peak_live_bytes[arm] = self.peak_live_bytes[arm].max(rest + bytes + variable);
            self.row_bytes[arm] += bytes;
        }
        self.reducer_coefficient_bytes += reducer_coefficient_bytes;
        self.batches += 1;
        self.wide_batches += usize::from(columns > U16_COLUMNS);
        self.layout_batches += usize::from(built);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A 64-bit field's 16-byte entry drops to 4 bytes per reducer entry when source-backed, to 10
    /// per entry split at u16, and to 2 per reducer entry with both.
    #[test]
    fn test_row_bytes_for_a_64_bit_field_in_a_narrow_batch() {
        assert_eq!(row_bytes(10, 100, 1_000, 8, 16), [1_760, 560, 1_100, 300]);
    }

    /// At 65,536 columns u16 still fits; at 65,537 both u16 arms fall back to u32 indices.
    #[test]
    fn test_u16_arms_fall_back_above_65536_columns() {
        assert_eq!(row_bytes(1, 1, 65_535, 4, 8), [16, 12, 12, 8]);
        assert_eq!(row_bytes(1, 1, 65_536, 4, 8), [16, 12, 12, 8]);
        assert_eq!(row_bytes(1, 1, 65_537, 4, 8), [16, 12, 16, 12]);
    }

    /// Every arm name parses to the arm at its own index.
    #[test]
    fn test_row_layout_names_round_trip() {
        for (k, name) in ARMS.iter().enumerate() {
            assert_eq!(RowLayout::parse(name).unwrap().index(), k);
        }
        assert_eq!(RowLayout::parse("u32"), None);
    }

    /// The census keeps each arm's largest batch, carrying the non-row charges and the reduced rows
    /// across unchanged, and counts wide batches.
    #[test]
    fn test_census_peaks_carry_the_unchanged_charges() {
        let mut c = LayoutCensus::default();
        c.record([100, 40, 60, 20], 50, 250, 10, 8, true);
        c.record([10, 4, 6, 2], 10, 10, U16_COLUMNS + 1, 0, false);
        assert_eq!(c.peak_live_bytes, [400, 340, 360, 320]);
        assert_eq!(c.row_bytes, [110, 44, 66, 22]);
        assert_eq!(
            (
                c.batches,
                c.wide_batches,
                c.reducer_coefficient_bytes,
                c.layout_batches
            ),
            (2, 1, 8, 1)
        );
    }
}
