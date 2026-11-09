//! Round-structured variable orders for CICO systems.
//!
//! The permutation machinery is [`VariableOrder`]; this decides *which* permutation, from a
//! cipher's round schedule.

use crate::grobner::transform::{ReorderError, VariableOrder};

/// Variables grouped by round, for a CICO system laid out as free inputs then S-box outputs.
///
/// The generated layout is `free_inputs` free variables followed by `per_round` S-box variables for
/// each of `rounds` rounds, in round order — see
/// [`CicoInstance::variables`](super::poseidon::CicoInstance::variables). Two reorderings of that
/// are natural to try and are not the same:
///
/// - [`RoundLayout::LastRoundFirst`] reverses the round blocks while keeping each block's internal
///   order, so the variables an output constraint touches directly come first.
/// - [`RoundLayout::FreeInputsLast`] moves the free inputs to the end, so the S-box chain leads.
///
/// Neither is a guess about which is better; §10.2 asks for at least two alternatives on
/// *identical mathematical systems*, and these are two whose construction can be stated in one
/// sentence each.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RoundLayout {
    /// The order the generator produces: free inputs, then S-box variables in round order.
    Generated,

    /// Free inputs, then the round blocks in reverse order, each block's internal order kept.
    LastRoundFirst,

    /// The S-box variables in round order, then the free inputs.
    FreeInputsLast,
}

impl RoundLayout {
    /// Every layout, for a sweep that should not need editing when one is added.
    pub const ALL: [Self; 3] = [Self::Generated, Self::LastRoundFirst, Self::FreeInputsLast];

    /// A short name.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Generated => "generated",
            Self::LastRoundFirst => "last-round-first",
            Self::FreeInputsLast => "free-inputs-last",
        }
    }

    /// The order this layout describes, for a system of `free_inputs` free variables followed by
    /// `blocks` blocks of S-box variables whose sizes are `block_sizes`.
    ///
    /// `block_sizes` rather than one width, because a Poseidon round schedule mixes full rounds
    /// (which introduce `t` S-box variables) with partial rounds (which introduce one). A single
    /// width would silently mis-group every instance with `R_P > 0`.
    ///
    /// # Errors
    /// [`ReorderError::NotAPermutation`] if the sizes do not account for exactly `N - free_inputs`
    /// variables.
    pub fn order<const N: usize>(
        &self,
        free_inputs: usize,
        block_sizes: &[usize],
    ) -> Result<VariableOrder<N>, ReorderError> {
        let accounted: usize = block_sizes.iter().sum();
        if free_inputs + accounted != N {
            return Err(ReorderError::NotAPermutation {
                length: N,
                offender: None,
            });
        }

        // The S-box variables, grouped into blocks in generated order.
        let mut blocks: Vec<Vec<usize>> = Vec::with_capacity(block_sizes.len());
        let mut next = free_inputs;
        for size in block_sizes {
            blocks.push((next..next + size).collect());
            next += size;
        }

        let free: Vec<usize> = (0..free_inputs).collect();
        let sources: Vec<usize> = match self {
            Self::Generated => free.iter().copied().chain(blocks.concat()).collect(),
            Self::LastRoundFirst => {
                blocks.reverse();
                free.iter().copied().chain(blocks.concat()).collect()
            }
            Self::FreeInputsLast => blocks.concat().into_iter().chain(free).collect(),
        };

        VariableOrder::new(self.name(), &sources)
    }
}

#[cfg(test)]
mod tests {
    use super::RoundLayout;
    use crate::{fields::Zp2147483647, FiniteField, Zero};

    type F = Zp2147483647;

    /// A round layout groups the S-box variables by round, with per-round sizes respected.
    ///
    /// The sizes matter: a Poseidon schedule mixes full rounds introducing `t` variables with
    /// partial rounds introducing one, so a single width would mis-group every instance with
    /// `R_P > 0`.
    #[test]
    fn test_round_layouts() {
        // Two free inputs, then blocks of 3, 1, 1, 3 — a `t = 3` schedule with one full round, two
        // partial rounds, and one full round. Nine variables.
        let sizes = [3usize, 1, 1, 3];

        let generated = RoundLayout::Generated
            .order::<10>(2, &sizes)
            .expect("the sizes account for eight variables");
        assert!(generated.is_identity());

        let last_first = RoundLayout::LastRoundFirst
            .order::<10>(2, &sizes)
            .expect("the sizes account for eight variables");
        // Free inputs 0,1; then the last block (7,8,9), then (6), then (5), then (2,3,4).
        assert_eq!(last_first.sources(), &[0, 1, 7, 8, 9, 6, 5, 2, 3, 4]);

        let inputs_last = RoundLayout::FreeInputsLast
            .order::<10>(2, &sizes)
            .expect("the sizes account for eight variables");
        assert_eq!(inputs_last.sources(), &[2, 3, 4, 5, 6, 7, 8, 9, 0, 1]);

        // Sizes that do not account for every variable are rejected rather than padded.
        assert!(RoundLayout::Generated.order::<10>(2, &[3, 1]).is_err());
        assert_eq!(RoundLayout::ALL.len(), 3);
    }

    /// Every layout is a genuine permutation and round-trips a point.
    #[test]
    fn test_every_layout_round_trips() {
        let sizes = [2usize, 1, 2];
        let point: [F; 6] = [
            F::new(1),
            F::new(2),
            F::new(3),
            F::new(4),
            F::new(5),
            F::new(6),
        ];
        for layout in RoundLayout::ALL {
            let order = layout
                .order::<6>(1, &sizes)
                .expect("the sizes account for five variables");
            assert_eq!(
                order.recover(&order.forward(&point)),
                point,
                "{}",
                layout.name()
            );
            // And a zero point stays zero, which catches an off-by-one that writes outside the
            // permutation's image.
            let zeros = [F::zero(); 6];
            assert_eq!(order.recover(&zeros), zeros, "{}", layout.name());
        }
    }
}
