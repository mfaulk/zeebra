use serde_json::{Value, json};
use std::cell::{Cell, RefCell};

#[derive(Clone, Copy)]
pub struct Policy {
    pub plain: bool,
    pub signature: bool,
    validate: bool,
    observe: bool,
}
impl Policy {
    pub fn named(name: &str, validate: bool) -> Result<Self, String> {
        let (plain, signature) = match name {
            "native" => (true, true),
            "no-plain" => (false, true),
            "no-signature" => (true, false),
            "none" => (false, false),
            _ => return Err(format!("unknown research policy: {name}")),
        };
        Ok(Self {
            plain,
            signature,
            validate,
            observe: false,
        })
    }
    pub fn observed(mut self, enabled: bool) -> Self {
        self.observe = enabled;
        self
    }
}
const NATIVE: Policy = Policy {
    plain: true,
    signature: true,
    validate: false,
    observe: false,
};
thread_local! {
    static POLICY: Cell<Policy> = const { Cell::new(NATIVE) };
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static EVENTS: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) };
    static AUDIT: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) };
}
pub fn capture<T>(policy: Policy, f: impl FnOnce() -> T) -> (T, Vec<Value>, Vec<Value>) {
    ACTIVE.with(|active| assert!(!active.replace(true), "nested randomization policy"));
    POLICY.with(|state| state.set(policy));
    AUDIT.with(|state| state.borrow_mut().clear());
    EVENTS.with(|state| state.borrow_mut().clear());
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            POLICY.with(|state| state.set(NATIVE));
            ACTIVE.with(|state| state.set(false));
            AUDIT.with(|state| state.borrow_mut().clear());
            EVENTS.with(|state| state.borrow_mut().clear());
        }
    }
    let reset = Reset;
    let value = f();
    let audit = AUDIT.with(|state| std::mem::take(&mut *state.borrow_mut()));
    let events = EVENTS.with(|state| std::mem::take(&mut *state.borrow_mut()));
    drop(reset);
    (value, audit, events)
}
pub(crate) fn plain_enabled() -> bool {
    POLICY.with(|p| p.get().plain)
}
pub(crate) fn signature_enabled() -> bool {
    POLICY.with(|p| p.get().signature)
}
pub(crate) fn validate_enabled() -> bool {
    POLICY.with(|p| p.get().validate)
}
pub(crate) fn block(rows: usize, pivots: usize, zeros: usize, requeued: bool) {
    if POLICY.with(|p| p.get().observe) {
        EVENTS.with(|state| {
            state
                .borrow_mut()
                .push(json!({"kind":"plain-block","rows":rows,
            "pivots":pivots,"zeros":zeros,"requeued":requeued}))
        });
    }
}
pub(crate) fn group(rows: usize, tests: usize, passed: bool) {
    if POLICY.with(|p| p.get().observe) {
        EVENTS.with(|state| {
            state
                .borrow_mut()
                .push(json!({"kind":"signature-group","rows":rows,
            "tests_required":tests,"passed":passed}))
        });
    }
}
pub(crate) fn checked(
    rows: usize,
    columns: usize,
    valid: bool,
    ns: u64,
    subtracted: u64,
    added: u64,
) {
    AUDIT.with(|state| {
        state
            .borrow_mut()
            .push(json!({"rows":rows,"columns":columns,
        "valid":valid,"nanoseconds":ns,"subtracted_entries":subtracted,"added_entries":added}))
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    // Independent controls preserve native behavior after returning or unwinding.
    #[test]
    fn policies_are_scoped_and_independent() {
        for (name, plain, signature) in [
            ("native", true, true),
            ("no-plain", false, true),
            ("no-signature", true, false),
            ("none", false, false),
        ] {
            let (_, audit, events) =
                capture(Policy::named(name, false).unwrap().observed(true), || {
                    assert_eq!(plain_enabled(), plain);
                    assert_eq!(signature_enabled(), signature);
                    checked(2, 3, true, 1, 0, 0);
                    block(64, 1, 2, false);
                    group(8, 3, true);
                });
            assert_eq!(audit.len(), 1);
            assert_eq!(events.len(), 2);
            assert!(plain_enabled() && signature_enabled() && !validate_enabled());
        }
        let _ = std::panic::catch_unwind(|| {
            capture(Policy::named("none", true).unwrap(), || panic!("stop"))
        });
        assert!(plain_enabled() && signature_enabled() && !validate_enabled());
    }
    // Unknown policy names are refused rather than silently enabling a different experiment.
    #[test]
    fn unknown_policy_is_rejected() {
        assert!(Policy::named("disabled", false).is_err());
    }
}
