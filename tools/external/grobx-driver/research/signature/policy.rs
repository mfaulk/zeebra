use serde_json::{Value, json};
use std::cell::Cell;

#[derive(Clone, Copy, Default)]
struct Plain {
    updates: u64,
    chain: u64,
    product: u64,
    lcm_redundant: u64,
    kept: u64,
}
thread_local! {
    static HANDOVER: Cell<bool> = const { Cell::new(true) };
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static PLAIN: Cell<Plain> = const { Cell::new(Plain { updates: 0, chain: 0, product: 0, lcm_redundant: 0, kept: 0 }) };
}
pub fn capture<T>(handover: bool, f: impl FnOnce() -> T) -> (T, Value) {
    ACTIVE.with(|active| assert!(!active.replace(true), "nested signature policy"));
    HANDOVER.with(|state| state.set(handover));
    PLAIN.with(|state| state.set(Plain::default()));
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            HANDOVER.with(|state| state.set(true));
            PLAIN.with(|state| state.set(Plain::default()));
            ACTIVE.with(|state| state.set(false));
        }
    }
    let reset = Reset;
    let value = f();
    let p = PLAIN.with(Cell::get);
    let observed = json!({"handover": handover, "plain_pairs": {"updates": p.updates,
        "chain_dropped": p.chain, "product_skipped": p.product,
        "lcm_redundant_skipped": p.lcm_redundant, "kept": p.kept}});
    drop(reset);
    (value, observed)
}
pub(crate) fn handover_enabled() -> bool {
    HANDOVER.with(Cell::get)
}
pub(crate) fn plain_update(chain: usize, product: usize, lcm_redundant: usize, kept: usize) {
    PLAIN.with(|state| {
        let mut p = state.get();
        p.updates += 1;
        p.chain += chain as u64;
        p.product += product as u64;
        p.lcm_redundant += lcm_redundant as u64;
        p.kept += kept as u64;
        state.set(p);
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    // The handover gate and plain pair tallies are scoped to one capture and reset after unwinding.
    #[test]
    fn gate_and_tallies_are_scoped() {
        let ((), seen) = capture(false, || {
            assert!(!handover_enabled());
            plain_update(1, 2, 3, 4);
            plain_update(1, 0, 0, 1);
        });
        assert_eq!(seen["handover"], false);
        assert_eq!(seen["plain_pairs"]["updates"], 2);
        assert_eq!(seen["plain_pairs"]["chain_dropped"], 2);
        assert_eq!(seen["plain_pairs"]["product_skipped"], 2);
        assert_eq!(seen["plain_pairs"]["lcm_redundant_skipped"], 3);
        assert_eq!(seen["plain_pairs"]["kept"], 5);
        assert!(handover_enabled());
        let _ = std::panic::catch_unwind(|| capture(false, || panic!("stop")));
        assert!(handover_enabled());
        let ((), seen) = capture(true, || {});
        assert_eq!(seen["plain_pairs"]["updates"], 0);
    }
}
