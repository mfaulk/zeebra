use std::{collections::HashSet, hash::Hash};

/// Returns true if the list contains duplicate entries.
pub fn contains_duplicates<T: Eq + Clone + Hash>(list: &[T]) -> bool {
    let num_inputs = list.len();
    let set: HashSet<T> = list.iter().cloned().collect();
    num_inputs != set.len()
}
