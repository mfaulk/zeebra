use std::time::Duration;
use zeebra::grobner::f4::StageTimings;

// Forward/backward refinements aggregate while elimination is counted only once.
#[test]
fn production_elimination_refinements_do_not_double_count() {
    let timings = StageTimings {
        elimination: Duration::from_millis(7),
        forward: Duration::from_millis(5),
        backward: Duration::from_millis(2),
        ..Default::default()
    };
    let mut total = StageTimings::default();
    total.add(&timings);
    assert_eq!(total.sum(), Duration::from_millis(7));
    assert_eq!(total.forward + total.backward, total.elimination);
}
