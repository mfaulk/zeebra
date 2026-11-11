//! Live entry and byte limits are coupled; report the binding allowance in its own unit.
//! Pressure uses observed maxima and cannot predict a system's eventual demand. Pair batch
//! caps shape the work rather than refusing it, so they have no budget-crossing report.

use std::fmt::{self, Display, Formatter};

use crate::{
    fields::FiniteField,
    grobner::f4::{F4Options, F4Statistics, StopKind},
};

/// What a budget allows, in the unit the budget is written in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Allowance {
    /// The option is `None`: nothing stops the computation on this axis.
    Unlimited,
    /// The allowance, in the line's [`unit`](BudgetLine::unit).
    Limit(usize),
}

impl Allowance {
    /// The allowance as a number, or `None` where there is no limit.
    pub fn limit(&self) -> Option<usize> {
        match self {
            Self::Unlimited => None,
            Self::Limit(limit) => Some(*limit),
        }
    }
}

impl Display for Allowance {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unlimited => write!(f, "unlimited"),
            Self::Limit(limit) => write!(f, "{limit}"),
        }
    }
}

/// One budget's allowance, and whether it is the one that can bind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BudgetLine {
    /// The [`F4Options`] field name, and the same string
    /// [`F4Error::limit_name`](super::F4Error::limit_name) reports — so a report and the refusal
    /// it anticipates name the budget identically.
    pub budget: &'static str,

    /// The allowance as written in the options.
    pub allowance: Allowance,

    /// What the allowance counts: `rows`, `columns`, `entries`, `bytes`, `batches`, `elements` or
    /// `ms`.
    pub unit: &'static str,

    /// False when another budget makes this one unreachable.
    ///
    /// Only the live pair can be non-binding: [`F4Options::max_live_nonzeros`] and
    /// [`F4Options::max_live_bytes`] bound the same quantity in two units and the effective limit
    /// is their `min`, so one of the two is always slack that never binds (#322). Every other
    /// budget bounds something no other budget does, and so is binding whenever it is set.
    pub binding: bool,

    /// Whether crossing this is a statement about the work or about the machine.
    ///
    /// [`StopKind::Time`] for [`F4Options::max_wall_time`], which is why it is reported here and
    /// never ranked against the rest: a wall clock is a fact about one box under one load.
    pub kind: StopKind,
}

/// Every budget an F4 configuration enforces, with the allowance that actually applies over `F`.
///
/// Produced by [`F4Options::budget_report`]. Answers the question #322 had to read the source for,
/// which is which of the two live budgets binds over the field in use and at what number.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BudgetReport {
    lines: Vec<BudgetLine>,
    bytes_per_entry: usize,
    live_entry_allowance: usize,
}

impl BudgetReport {
    /// Every budget, in the order the options declare them.
    pub fn lines(&self) -> &[BudgetLine] {
        &self.lines
    }

    /// `size_of::<(usize, F)>()` for the field the report was taken over.
    ///
    /// 16 bytes over a 64-bit prime field and 40 over a 254-bit one, which is why an entry budget
    /// alone means something different at every field width.
    pub fn bytes_per_entry(&self) -> usize {
        self.bytes_per_entry
    }

    /// The live entries admitted over `F`: the `min` of the two live budgets, in entries.
    pub fn live_entry_allowance(&self) -> usize {
        self.live_entry_allowance
    }

    /// The line for `budget`, which is a field name as [`BudgetLine::budget`] spells it.
    pub fn line(&self, budget: &str) -> Option<&BudgetLine> {
        self.lines.iter().find(|line| line.budget == budget)
    }

    /// The budgets that can bind: everything set, less the slack half of the live pair.
    pub fn binding(&self) -> impl Iterator<Item = &BudgetLine> {
        self.lines
            .iter()
            .filter(|line| line.binding && line.allowance.limit().is_some())
    }
}

impl Display for BudgetReport {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "F4 budgets at {} bytes per live entry; {} live entries admitted",
            self.bytes_per_entry, self.live_entry_allowance
        )?;
        for line in &self.lines {
            writeln!(
                f,
                "  {:<20} {:>14} {:<8} {}",
                line.budget,
                line.allowance.to_string(),
                line.unit,
                match (line.allowance, line.binding) {
                    (Allowance::Unlimited, _) => "no limit",
                    (_, true) => "binds",
                    (_, false) => "slack: the other live budget binds first",
                }
            )?;
        }
        Ok(())
    }
}

/// How close a completed or refused run came to one budget.
///
/// Produced by [`F4Statistics::budget_pressure`]. `observed` is a high-water mark over the batches
/// that *completed*, so for a refused run it describes the batches before the one that crossed —
/// which is the point: it turns "refused at batch 41" into "batch 39 was already at 98%".
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BudgetApproach {
    /// The budget's field name, as [`BudgetLine::budget`] spells it.
    pub budget: &'static str,

    /// The high-water mark the run reached, in [`unit`](Self::unit).
    pub observed: usize,

    /// The allowance it was measured against, in [`unit`](Self::unit).
    ///
    /// The *effective* allowance, so for the live pair this is the `min` of the two budgets and
    /// `budget` names whichever of them produced it.
    pub allowance: usize,

    /// What both figures count. See [`BudgetLine::unit`].
    pub unit: &'static str,
}

impl BudgetApproach {
    /// Observed over allowed, as a fraction. 1.0 or above means the budget was reached.
    ///
    /// Never divides by zero: [`F4Statistics::budget_pressure`] omits a budget whose allowance is
    /// zero, since every run crosses it and the ratio says nothing.
    pub fn utilisation(&self) -> f64 {
        self.observed as f64 / self.allowance as f64
    }
}

impl Display for BudgetApproach {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at {:.1}% ({} of {} {})",
            self.budget,
            100.0 * self.utilisation(),
            self.observed,
            self.allowance,
            self.unit
        )
    }
}

impl F4Options {
    /// Every budget this configuration enforces over `F`, and the allowance that applies.
    ///
    /// The cheap half of #468: no computation runs, so this answers "what are my limits" and not
    /// "will this system cross them" — F4's row and column counts are discovered by symbolic
    /// preprocessing rather than being a function of the input, so the second question has no
    /// cheap answer and this does not pretend to give one. For how close a run actually came, see
    /// [`F4Statistics::budget_pressure`].
    ///
    /// Generic over `F` because the live pair's coupling is: `512_000_000 / 16` is exactly
    /// `32_000_000`, so at [`recommended`](Self::recommended) the two budgets are the same number
    /// over a 64-bit field and `max_live_bytes` binds alone over a 254-bit one.
    pub fn budget_report<F: FiniteField>(&self) -> BudgetReport {
        let bytes_per_entry = Self::bytes_per_entry::<F>();
        let bytes_bind = self.bytes_bind_first::<F>();
        BudgetReport {
            lines: vec![
                BudgetLine {
                    budget: "max_matrix_rows",
                    allowance: Allowance::Limit(self.max_matrix_rows),
                    unit: "rows",
                    binding: true,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_matrix_columns",
                    allowance: Allowance::Limit(self.max_matrix_columns),
                    unit: "columns",
                    binding: true,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_live_nonzeros",
                    allowance: Allowance::Limit(self.max_live_nonzeros),
                    unit: "entries",
                    binding: !bytes_bind,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_live_bytes",
                    allowance: Allowance::Limit(self.max_live_bytes),
                    unit: "bytes",
                    binding: bytes_bind,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_batches",
                    allowance: allowance_of(self.max_batches),
                    unit: "batches",
                    binding: true,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_basis_elements",
                    allowance: allowance_of(self.max_basis_elements),
                    unit: "elements",
                    binding: true,
                    kind: StopKind::Resource,
                },
                BudgetLine {
                    budget: "max_wall_time",
                    allowance: allowance_of(
                        self.max_wall_time
                            .map(|d| d.as_millis().min(usize::MAX as u128) as usize),
                    ),
                    unit: "ms",
                    binding: true,
                    kind: StopKind::Time,
                },
            ],
            bytes_per_entry,
            live_entry_allowance: self.live_entry_allowance::<F>(),
        }
    }
}

/// `Some(n)` as a limit, `None` as unlimited.
fn allowance_of(limit: Option<usize>) -> Allowance {
    match limit {
        Some(limit) => Allowance::Limit(limit),
        None => Allowance::Unlimited,
    }
}

impl F4Statistics {
    /// How close this run came to each resource budget, worst first.
    ///
    /// The other half of #468, and the one that needs no dry run: every figure below is a
    /// high-water mark the batch loop already recorded, so a caller gets the answer from the
    /// statistics it is handed whether the run finished or was refused.
    ///
    /// Omits [`F4Options::max_wall_time`] — the statistics hold no elapsed time unless
    /// [`measure_stages`](F4Options::measure_stages) is set, and a clock is
    /// [`StopKind::Time`] rather than a budget on the work, so ranking it beside an entry count
    /// would make the ordering depend on how busy the box was. Omits unlimited budgets, where a
    /// fraction has no meaning, and zero allowances, which every run crosses.
    ///
    /// Empty for a run that built no matrix: [`bytes_per_entry`](Self::bytes_per_entry) is unset
    /// there, so the live pair's effective allowance is not yet known and there is no observation
    /// to divide by either.
    pub fn budget_pressure(&self, options: &F4Options) -> Vec<BudgetApproach> {
        if self.batches == 0 || self.bytes_per_entry == 0 {
            return Vec::new();
        }

        // The live pair reports as one line under whichever name bound, matching the error
        // `F4Options::entry_budget_error` would have raised — in bytes when bytes bound, so the
        // figure and the name are in the same unit.
        let entries = options.live_entry_allowance_for(self.bytes_per_entry);
        let live = if options.bytes_bind_first_for(self.bytes_per_entry) {
            BudgetApproach {
                budget: "max_live_bytes",
                observed: self.max_live_nonzeros.saturating_mul(self.bytes_per_entry),
                allowance: options.max_live_bytes,
                unit: "bytes",
            }
        } else {
            BudgetApproach {
                budget: "max_live_nonzeros",
                observed: self.max_live_nonzeros,
                allowance: entries,
                unit: "entries",
            }
        };

        let mut approaches = vec![
            BudgetApproach {
                budget: "max_matrix_rows",
                observed: self.max_matrix_rows,
                allowance: options.max_matrix_rows,
                unit: "rows",
            },
            BudgetApproach {
                budget: "max_matrix_columns",
                observed: self.max_matrix_columns,
                allowance: options.max_matrix_columns,
                unit: "columns",
            },
            live,
        ];
        if let Some(limit) = options.max_batches {
            approaches.push(BudgetApproach {
                budget: "max_batches",
                observed: self.batches,
                allowance: limit,
                unit: "batches",
            });
        }
        if let Some(limit) = options.max_basis_elements {
            approaches.push(BudgetApproach {
                budget: "max_basis_elements",
                observed: self.peak_basis_elements,
                allowance: limit,
                unit: "elements",
            });
        }

        approaches.retain(|approach| approach.allowance > 0);
        // Descending by utilisation, which is a ratio rather than a count: the budget with the
        // largest absolute headroom is not the one about to bind. `total_cmp` rather than
        // `partial_cmp`, so no NaN can make the order depend on the sort's pivot choices.
        approaches.sort_by(|a, b| b.utilisation().total_cmp(&a.utilisation()));
        approaches
    }

    /// The budgets this run came within `threshold` of, worst first.
    ///
    /// `threshold` is a fraction of the allowance: `0.8` reports every budget at or above 80%. The
    /// warning #468 asked for — a run approaching a budget says so instead of only a run that
    /// crossed one.
    pub fn near_budget(&self, options: &F4Options, threshold: f64) -> Vec<BudgetApproach> {
        let mut approaches = self.budget_pressure(options);
        approaches.retain(|approach| approach.utilisation() >= threshold);
        approaches
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;
    use crate::{
        fields::{Bn254Fr, Zp13},
        grobner::f4::statistics::BatchStatistics,
        linalg::sparse::EliminationStatistics,
    };

    /// `budget_report` names every budget F4 can refuse on, and only those.
    #[test]
    fn test_budget_report_covers_every_refusable_budget() {
        let report = F4Options::recommended().budget_report::<Zp13>();
        let named: Vec<&str> = report.lines().iter().map(|line| line.budget).collect();
        assert_eq!(
            named,
            vec![
                "max_matrix_rows",
                "max_matrix_columns",
                "max_live_nonzeros",
                "max_live_bytes",
                "max_batches",
                "max_basis_elements",
                "max_wall_time",
            ]
        );
    }

    /// At `recommended` over a 16-byte entry the two live budgets are equal, so the older one is
    /// reported as binding and the byte budget as slack — the coupling #322 had to read the source
    /// to discover.
    #[test]
    fn test_the_report_says_which_live_budget_binds_over_a_narrow_field() {
        let report = F4Options::recommended().budget_report::<Zp13>();
        assert_eq!(report.bytes_per_entry(), 16);
        assert_eq!(report.live_entry_allowance(), 32_000_000);
        assert!(report.line("max_live_nonzeros").expect("the line").binding);
        assert!(!report.line("max_live_bytes").expect("the line").binding);
    }

    /// Over a 254-bit field an entry costs 40 bytes, so the byte budget binds at two fifths of the
    /// entry budget and the report says so without a run.
    #[test]
    fn test_the_report_says_which_live_budget_binds_over_a_wide_field() {
        let report = F4Options::recommended().budget_report::<Bn254Fr>();
        assert_eq!(report.bytes_per_entry(), 40);
        assert_eq!(report.live_entry_allowance(), 512_000_000 / 40);
        assert!(!report.line("max_live_nonzeros").expect("the line").binding);
        assert!(report.line("max_live_bytes").expect("the line").binding);
    }

    /// An unset budget reports as unlimited and is excluded from the binding set, so a caller
    /// reading the report cannot mistake `None` for a limit of zero.
    #[test]
    fn test_unset_budgets_report_as_unlimited() {
        let options = F4Options::recommended();
        let report = options.budget_report::<Zp13>();
        assert_eq!(
            report.line("max_batches").expect("the line").allowance,
            Allowance::Unlimited
        );
        assert_eq!(
            report
                .line("max_batches")
                .expect("the line")
                .allowance
                .limit(),
            None
        );
        let binding: Vec<&str> = report.binding().map(|line| line.budget).collect();
        assert_eq!(
            binding,
            vec!["max_matrix_rows", "max_matrix_columns", "max_live_nonzeros"]
        );
    }

    /// The wall clock is reported, and reported as a time stop rather than a resource one, so a
    /// consumer ranking resource budgets does not rank a fact about one machine beside them.
    #[test]
    fn test_the_wall_clock_is_reported_as_a_time_stop() {
        let options = F4Options {
            max_wall_time: Some(Duration::from_millis(2500)),
            ..F4Options::recommended()
        };
        let line = options
            .budget_report::<Zp13>()
            .line("max_wall_time")
            .copied()
            .expect("the line");
        assert_eq!(line.allowance, Allowance::Limit(2500));
        assert_eq!(line.kind, StopKind::Time);
        assert_eq!(line.unit, "ms");
    }

    /// One batch at the given shape, which is all `budget_pressure` reads.
    fn statistics_at(rows: usize, columns: usize, peak_nonzeros: usize) -> F4Statistics {
        let batch = BatchStatistics {
            rows,
            columns,
            bytes_per_entry: 16,
            elimination: EliminationStatistics {
                peak_nonzeros,
                initial_nonzeros: peak_nonzeros,
                ..EliminationStatistics::default()
            },
            ..BatchStatistics::default()
        };
        let mut statistics = F4Statistics::default();
        statistics.record(&batch);
        statistics
    }

    /// A run that came within 1% of the live budget says so, ranked above the budgets it had
    /// headroom on — the "batch 39 was at 98%" the issue asked for.
    #[test]
    fn test_budget_pressure_ranks_the_budget_that_was_nearly_crossed_first() {
        let options = F4Options::recommended();
        let statistics = statistics_at(100, 100, 31_680_000);

        let pressure = statistics.budget_pressure(&options);
        assert_eq!(pressure[0].budget, "max_live_nonzeros");
        assert_eq!(pressure[0].observed, 31_680_000);
        assert_eq!(pressure[0].allowance, 32_000_000);
        assert!((pressure[0].utilisation() - 0.99).abs() < 1e-9);

        // Still reported, and below it: 100 of 200 000 rows is 0.05%.
        let rows = pressure
            .iter()
            .find(|approach| approach.budget == "max_matrix_rows")
            .expect("rows are always budgeted");
        assert!(rows.utilisation() < pressure[0].utilisation());
    }

    /// `near_budget` reports only what crossed the threshold, so a caller can warn without
    /// re-deriving the ratios.
    #[test]
    fn test_near_budget_filters_on_the_threshold() {
        let options = F4Options::recommended();
        let statistics = statistics_at(100, 100, 31_680_000);

        let near: Vec<&str> = statistics
            .near_budget(&options, 0.9)
            .iter()
            .map(|approach| approach.budget)
            .collect();
        assert_eq!(near, vec!["max_live_nonzeros"]);
        assert!(statistics.near_budget(&options, 0.999).is_empty());
    }

    /// Pressure on the live pair is reported in the unit of whichever budget bound, so the figure
    /// and the name agree — bytes when `max_live_bytes` binds.
    #[test]
    fn test_pressure_on_the_live_pair_is_reported_in_the_binding_budget_s_unit() {
        let options = F4Options {
            max_live_nonzeros: 100_000_000,
            ..F4Options::recommended()
        };
        let statistics = statistics_at(10, 10, 19_000_000);

        let live = statistics
            .budget_pressure(&options)
            .into_iter()
            .find(|approach| approach.budget == "max_live_bytes")
            .expect("bytes bind once the entry budget is lifted alone");
        assert_eq!(live.unit, "bytes");
        assert_eq!(live.observed, 19_000_000 * 16);
        assert_eq!(live.allowance, 512_000_000);
    }

    /// A run that built no matrix has nothing to report, rather than reporting zero pressure
    /// against an allowance derived from an unknown entry width.
    #[test]
    fn test_a_run_with_no_batches_reports_no_pressure() {
        assert!(F4Statistics::default()
            .budget_pressure(&F4Options::recommended())
            .is_empty());
    }

    /// Unlimited budgets are omitted from the pressure report, since a fraction of no limit is not
    /// a number a caller could act on.
    #[test]
    fn test_unlimited_budgets_are_omitted_from_the_pressure_report() {
        let statistics = statistics_at(10, 10, 1_000);
        let unbounded: Vec<&str> = statistics
            .budget_pressure(&F4Options::recommended())
            .iter()
            .map(|approach| approach.budget)
            .collect();
        assert!(!unbounded.contains(&"max_batches"));
        assert!(!unbounded.contains(&"max_basis_elements"));

        let options = F4Options {
            max_batches: Some(4),
            max_basis_elements: Some(8),
            ..F4Options::recommended()
        };
        let bounded: Vec<&str> = statistics
            .budget_pressure(&options)
            .iter()
            .map(|approach| approach.budget)
            .collect();
        assert!(bounded.contains(&"max_batches"));
        assert!(bounded.contains(&"max_basis_elements"));
    }
}
