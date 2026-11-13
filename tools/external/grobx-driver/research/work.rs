use serde_json::{Value, json};
use std::cell::RefCell;

#[derive(Clone, Copy, Default)]
struct Counts {
    calls: u64,
    products: u64,
    useful_products: u64,
    source_entries: u64,
    loaded: u64,
    takes: u64,
    direct_mul: u64,
    charged_subtractions: u64,
    charged_entries: u64,
}

impl Counts {
    fn json(self) -> Value {
        json!({"row_kernel_calls": self.calls, "executed_lane_products": self.products,
            "nonzero_multiplier_products": self.useful_products,
            "source_entries_read": self.source_entries, "loaded_entries": self.loaded,
            "dense_take_calls": self.takes, "direct_field_mul_calls": self.direct_mul,
            "subtraction_budget_calls": self.charged_subtractions,
            "subtracted_entry_charges": self.charged_entries})
    }
}

pub struct Summary {
    matrices: Vec<Value>,
    outside: Counts,
    current: Option<Matrix>,
    phase: usize,
}

struct Matrix {
    index: usize,
    rows: usize,
    given: usize,
    columns: usize,
    initial_entries: usize,
    phases: [Counts; 3],
    peak: Value,
    peak_capacity: usize,
    peak_stored_entries: usize,
}

thread_local! {
    static STATE: RefCell<Option<Summary>> = const { RefCell::new(None) };
}

pub fn capture<T>(enabled: bool, f: impl FnOnce() -> T) -> (T, Option<Summary>) {
    if !enabled {
        return (f(), None);
    }
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        assert!(state.is_none(), "nested work counter capture");
        *state = Some(Summary {
            matrices: Vec::new(),
            outside: Counts::default(),
            current: None,
            phase: 0,
        });
    });
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            STATE.with(|state| {
                state.borrow_mut().take();
            });
        }
    }
    let reset = Reset;
    let value = f();
    let summary = STATE.with(|state| state.borrow_mut().take());
    drop(reset);
    (value, summary)
}

pub(crate) fn enabled() -> bool {
    STATE.with(|state| state.borrow().is_some())
}

fn count(f: impl FnOnce(&mut Counts)) {
    STATE.with(|state| {
        if let Some(s) = state.borrow_mut().as_mut() {
            let c = s
                .current
                .as_mut()
                .map_or(&mut s.outside, |m| &mut m.phases[s.phase]);
            f(c);
        }
    });
}

pub(crate) fn products(entries: usize, lanes: usize, nonzero: usize) {
    count(|c| {
        c.calls += 1;
        c.products += (entries * lanes) as u64;
        c.useful_products += (entries * nonzero) as u64;
        c.source_entries += entries as u64;
    });
}
pub(crate) fn load(entries: usize) {
    count(|c| c.loaded += entries as u64);
}
pub(crate) fn take() {
    count(|c| c.takes += 1);
}
pub(crate) fn direct_mul() {
    count(|c| c.direct_mul += 1);
}
pub(crate) fn subtraction(entries: usize) {
    count(|c| {
        c.charged_subtractions += 1;
        c.charged_entries += entries as u64;
    });
}
pub(crate) fn phase(phase: usize) {
    STATE.with(|state| {
        if let Some(s) = state.borrow_mut().as_mut() {
            s.phase = phase;
        }
    });
}
pub(crate) fn begin(rows: usize, given: usize, columns: usize, initial_entries: usize) {
    STATE.with(|state| {
        if let Some(s) = state.borrow_mut().as_mut() {
            assert!(s.current.is_none(), "a matrix was not closed");
            s.phase = 0;
            s.current = Some(Matrix {
                index: s.matrices.len(),
                rows,
                given,
                columns,
                initial_entries,
                phases: [Counts::default(); 3],
                peak: Value::Null,
                peak_capacity: 0,
                peak_stored_entries: 0,
            });
        }
    });
}

pub(crate) fn memory(
    original_entries: usize,
    original_capacity: usize,
    made_entries: usize,
    made_capacity: usize,
    workspace_entries: usize,
    workspace_capacity: usize,
    transient_entries: usize,
    transient_capacity: usize,
) {
    STATE.with(|state| {
        if let Some(m) = state.borrow_mut().as_mut().and_then(|s| s.current.as_mut()) {
            let total = original_capacity + made_capacity + workspace_capacity + transient_capacity;
            m.peak_stored_entries = m
                .peak_stored_entries
                .max(original_entries + made_entries + workspace_entries + transient_entries);
            if total > m.peak_capacity {
                m.peak_capacity = total;
                m.peak = json!({"original_column_entries": original_entries,
                    "original_column_capacity_bytes": original_capacity,
                    "made_entries": made_entries, "made_capacity_bytes": made_capacity,
                    "workspace_stored_sparse_entries": workspace_entries,
                    "workspace_capacity_bytes": workspace_capacity,
                    "transient_entries": transient_entries,
                    "transient_capacity_bytes": transient_capacity,
                    "total_capacity_bytes": total});
            }
        }
    });
}

pub(crate) fn end() {
    STATE.with(|state| {
        if let Some(s) = state.borrow_mut().as_mut()
            && let Some(m) = s.current.take()
        {
            s.matrices
                .push(json!({"index": m.index, "rows": m.rows, "given": m.given,
                "columns": m.columns, "initial_entries": m.initial_entries,
                "forward": m.phases[0].json(), "backsub": m.phases[1].json(),
                "combination": m.phases[2].json(),
                "peak_accounted_capacity_bytes": m.peak_capacity,
                "peak_stored_sparse_entries": m.peak_stored_entries,
                "at_capacity_peak": m.peak}));
            s.phase = 0;
        }
    });
}
impl Summary {
    pub fn json(mut self) -> Value {
        // A stopped matrix is retained as partial rather than silently discarded.
        if let Some(m) = self.current.take() {
            self.matrices.push(json!({"index": m.index, "partial": true,
                "rows": m.rows, "columns": m.columns,
                "forward": m.phases[0].json(), "backsub": m.phases[1].json(),
                "combination": m.phases[2].json(), "at_capacity_peak": m.peak}));
        }
        json!({"schema": 1, "coverage": "Gf31 field kernels; all matrix reducers",
            "matrices": self.matrices, "outside_matrix": self.outside.json(),
            "limits": "Capacity is reserved bytes, not RSS. Dense/band scratch bytes are allocated capacity, not live nonzeros. Excludes basis/shared coefficients, monomial table, row headers, pivot maps, allocator overhead and input-echelon merge arithmetic. Captures materialized sparse rows and construction copies at row boundaries; no claim of instruction/DRAM traffic counts."})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        field::{Field, Gf31},
        id::MonoId,
    };

    // Sparse scalar and four-lane kernels count executed products separately from nonzero multipliers.
    #[test]
    fn exact_products_distinguish_zero_simd_lanes() {
        let f = Gf31::new(13).unwrap();
        let cols = [MonoId::from_raw(0), MonoId::from_raw(3)];
        let coefs = [2, 4];
        let (_, s) = capture(true, || {
            let mut dense = [0; 8];
            let mut band = [[0; 4]; 8];
            unsafe {
                f.load(&mut dense, &cols, &coefs);
                f.sub_mul(&mut dense, &cols, &coefs, 3);
                f.sub_mul_band(&mut band, &cols, &coefs, &[1, 0, 2, 0]);
                f.sub_mul_band_row(&mut band, 0, &cols, &coefs, 3);
            }
            f.take(&mut dense[0]);
        });
        let c = s.unwrap().json()["outside_matrix"].clone();
        assert_eq!(c["row_kernel_calls"], 3);
        assert_eq!(c["executed_lane_products"], 12);
        assert_eq!(c["nonzero_multiplier_products"], 8);
        assert_eq!(c["source_entries_read"], 6);
        assert_eq!(c["loaded_entries"], 2);
        assert_eq!(c["dense_take_calls"], 1);
        let (_, off) = capture(false, || products(100, 4, 4));
        assert!(off.is_none());
    }

    // A capacity snapshot records simultaneous roles and keeps independent stored-entry high waters.
    #[test]
    fn simultaneous_capacity_snapshot_is_not_sum_of_independent_peaks() {
        let (_, s) = capture(true, || {
            begin(3, 2, 8, 4);
            memory(4, 16, 2, 16, 1, 64, 3, 24);
            memory(4, 16, 8, 32, 6, 32, 4, 16);
            end();
        });
        let m = s.unwrap().json()["matrices"][0].clone();
        assert_eq!(m["peak_accounted_capacity_bytes"], 120);
        assert_eq!(m["peak_stored_sparse_entries"], 22);
        assert_eq!(m["at_capacity_peak"]["made_entries"], 2);
        assert_eq!(m["at_capacity_peak"]["total_capacity_bytes"], 120);
    }
}
