/// What an FGLM conversion did.
///
/// The quotient dimension is the figure to quote: FGLM's cost is `O(N * D^3)` with dense linear
/// algebra, so `D` explains a timing where the variable count does not. The rest attributes that
/// cost between the frontier, the operators, and the dependence test.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FglmStatistics {
    /// `D = dim_F(R/I)`, and therefore also the number of target standard monomials.
    pub quotient_dimension: usize,

    /// Elements of the source basis.
    pub source_basis_elements: usize,

    /// Elements of the target basis, i.e. relations emitted.
    pub target_basis_elements: usize,

    /// Entries the `N` multiplication operators hold between them.
    pub operator_entries: usize,

    /// Candidate monomials taken off the frontier.
    pub candidates_considered: usize,

    /// Candidates discarded because an already-emitted leading monomial divided them.
    ///
    /// Pruning is what keeps the frontier finite; a conversion where this is zero either found no
    /// relations or has a bug.
    pub candidates_pruned: usize,

    /// Candidates whose quotient vector extended the span. Equals `quotient_dimension` on success.
    pub candidates_independent: usize,

    /// Candidates whose quotient vector was dependent, each producing one relation.
    pub candidates_dependent: usize,

    /// Row subtractions performed by the dependence test. Each touches `2 * D` entries.
    pub span_row_operations: usize,
}
