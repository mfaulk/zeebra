//! A bounded zero-suppressed decision diagram manager for Boolean polynomials.
//!
//! A node `(level, hi, lo)` is the polynomial `x·hi + lo`, where `x` is the variable at `level`
//! and neither branch mentions a level at or above it. Two rules make the diagram canonical
//! (Minato's ZDD, as PolyBoRi uses it): a node whose `hi` is the zero terminal is not built, its
//! `lo` stands for it; and the unique table returns the existing node for a repeated triple. So
//! two polynomials are equal exactly when their roots are the same id.
//!
//! The manager never frees a node, so allocated nodes are also the peak. Both the node count and
//! the operation cache are bounded, and exceeding either is a typed refusal: a result the
//! prototype cannot finish is never returned truncated.

use std::collections::HashMap;

use super::anf::{Anf, Term};
use super::{VariableOrder, ZddError};

/// A node id. [`ZERO`] and [`ONE`] are the terminals.
pub type NodeId = u32;
/// The zero polynomial.
pub const ZERO: NodeId = 0;
/// The constant `1`.
pub const ONE: NodeId = 1;
const TERMINAL_LEVEL: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
struct Node {
    level: u32,
    hi: NodeId,
    lo: NodeId,
}

/// The manager's limits.
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    /// Most decision nodes that may be allocated.
    pub max_nodes: usize,
    /// Most operation-cache entries, counted across every operation.
    pub max_cache_entries: usize,
}

/// Counters for the measurements.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ZddStats {
    /// Unique-table probes.
    pub unique_lookups: u64,
    /// Probes that found an existing node.
    pub unique_hits: u64,
    /// Operation-cache probes.
    pub cache_lookups: u64,
    /// Probes that found a result.
    pub cache_hits: u64,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Op {
    Xor,
    Mul,
    NormalForm,
}

/// The manager: node store, unique table, operation cache.
pub struct Zdd {
    order: VariableOrder,
    nodes: Vec<Node>,
    unique: HashMap<(u32, NodeId, NodeId), NodeId>,
    cache: HashMap<(Op, NodeId, NodeId), NodeId>,
    budget: Budget,
    stats: ZddStats,
    /// Rule tails by level, for the normal form; set by `super::normal_form`.
    pub(super) tails: Vec<Option<NodeId>>,
}

impl Zdd {
    /// An empty manager over `order`.
    pub fn new(order: VariableOrder, budget: Budget) -> Self {
        let terminal = Node {
            level: TERMINAL_LEVEL,
            hi: ZERO,
            lo: ZERO,
        };
        let n = order.len();
        Self {
            order,
            nodes: vec![terminal, terminal],
            unique: HashMap::new(),
            cache: HashMap::new(),
            budget,
            stats: ZddStats::default(),
            tails: vec![None; n],
        }
    }

    /// The variable order.
    pub fn order(&self) -> &VariableOrder {
        &self.order
    }

    /// The counters so far.
    pub fn stats(&self) -> ZddStats {
        self.stats
    }

    /// Decision nodes allocated. Nothing is freed, so this is also the peak.
    pub fn allocated_nodes(&self) -> usize {
        self.nodes.len() - 2
    }

    /// Operation-cache entries held.
    pub fn cache_entries(&self) -> usize {
        self.cache.len()
    }

    /// Estimated heap bytes held, from the tables' capacities.
    pub fn heap_bytes(&self) -> usize {
        use std::mem::size_of;
        self.nodes.capacity() * size_of::<Node>()
            + self.unique.capacity() * (size_of::<((u32, NodeId, NodeId), NodeId)>() + 1)
            + self.cache.capacity() * (size_of::<((Op, NodeId, NodeId), NodeId)>() + 1)
    }

    pub(super) fn level(&self, f: NodeId) -> u32 {
        self.nodes[f as usize].level
    }

    pub(super) fn branches(&self, f: NodeId) -> (NodeId, NodeId) {
        let n = self.nodes[f as usize];
        (n.hi, n.lo)
    }

    /// `x_level·hi + lo`, where neither branch mentions `level` or anything above it.
    pub(super) fn mk(&mut self, level: u32, hi: NodeId, lo: NodeId) -> Result<NodeId, ZddError> {
        debug_assert!(level < self.level(hi) && level < self.level(lo));
        if hi == ZERO {
            return Ok(lo);
        }
        self.stats.unique_lookups += 1;
        if let Some(&id) = self.unique.get(&(level, hi, lo)) {
            self.stats.unique_hits += 1;
            return Ok(id);
        }
        if self.allocated_nodes() >= self.budget.max_nodes {
            return Err(ZddError::NodeBudgetExceeded {
                limit: self.budget.max_nodes,
            });
        }
        let id = self.nodes.len() as NodeId;
        self.nodes.push(Node { level, hi, lo });
        self.unique.insert((level, hi, lo), id);
        Ok(id)
    }

    pub(super) fn cached(&mut self, key: (Op, NodeId, NodeId)) -> Option<NodeId> {
        self.stats.cache_lookups += 1;
        let hit = self.cache.get(&key).copied();
        self.stats.cache_hits += hit.is_some() as u64;
        hit
    }

    pub(super) fn remember(
        &mut self,
        key: (Op, NodeId, NodeId),
        r: NodeId,
    ) -> Result<(), ZddError> {
        if self.cache.len() >= self.budget.max_cache_entries {
            return Err(ZddError::CacheBudgetExceeded {
                limit: self.budget.max_cache_entries,
            });
        }
        self.cache.insert(key, r);
        Ok(())
    }

    /// The variable `x_v`.
    pub fn var(&mut self, v: u32) -> Result<NodeId, ZddError> {
        self.mk(self.order.level_of(v), ONE, ZERO)
    }

    /// The sum `f + g`.
    pub fn xor(&mut self, f: NodeId, g: NodeId) -> Result<NodeId, ZddError> {
        if f == ZERO {
            return Ok(g);
        }
        if g == ZERO {
            return Ok(f);
        }
        if f == g {
            return Ok(ZERO);
        }
        let (f, g) = (f.min(g), f.max(g));
        if let Some(r) = self.cached((Op::Xor, f, g)) {
            return Ok(r);
        }
        let (lf, lg) = (self.level(f), self.level(g));
        let r = if lf < lg {
            let (hi, lo) = self.branches(f);
            let lo = self.xor(lo, g)?;
            self.mk(lf, hi, lo)?
        } else if lg < lf {
            let (hi, lo) = self.branches(g);
            let lo = self.xor(f, lo)?;
            self.mk(lg, hi, lo)?
        } else {
            let ((fh, fl), (gh, gl)) = (self.branches(f), self.branches(g));
            let hi = self.xor(fh, gh)?;
            let lo = self.xor(fl, gl)?;
            self.mk(lf, hi, lo)?
        };
        self.remember((Op::Xor, f, g), r)?;
        Ok(r)
    }

    /// The Boolean product `f·g`, where `x·x = x`.
    ///
    /// With `x` the top variable, `f = x·f1 + f0` and `g = x·g1 + g0`, so
    /// `f·g = x·(f1·g1 + f1·g0 + f0·g1) + f0·g0`: the square `x^2` folds into `x` here, which is
    /// the whole difference from the polynomial-ring product.
    pub fn mul(&mut self, f: NodeId, g: NodeId) -> Result<NodeId, ZddError> {
        if f == ZERO || g == ZERO {
            return Ok(ZERO);
        }
        if f == ONE {
            return Ok(g);
        }
        if g == ONE || f == g {
            return Ok(f);
        }
        let (f, g) = (f.min(g), f.max(g));
        if let Some(r) = self.cached((Op::Mul, f, g)) {
            return Ok(r);
        }
        let level = self.level(f).min(self.level(g));
        let (f1, f0) = self.split(f, level);
        let (g1, g0) = self.split(g, level);
        let low = self.mul(f0, g0)?;
        let a = self.mul(f1, g1)?;
        let b = self.mul(f1, g0)?;
        let c = self.mul(f0, g1)?;
        let hi = self.xor(a, b)?;
        let hi = self.xor(hi, c)?;
        let r = self.mk(level, hi, low)?;
        self.remember((Op::Mul, f, g), r)?;
        Ok(r)
    }

    /// `(f1, f0)` with `f = x_level·f1 + f0`, for `level` at or above `f`'s top.
    fn split(&self, f: NodeId, level: u32) -> (NodeId, NodeId) {
        if self.level(f) == level {
            self.branches(f)
        } else {
            (ZERO, f)
        }
    }

    /// `f` with `x_v ← h`. `h` may mention any variable, `x_v` included.
    pub fn substitute(&mut self, f: NodeId, v: u32, h: NodeId) -> Result<NodeId, ZddError> {
        let target = self.order.level_of(v);
        let mut memo = HashMap::new();
        self.substitute_rec(f, target, h, &mut memo)
    }

    fn substitute_rec(
        &mut self,
        f: NodeId,
        target: u32,
        h: NodeId,
        memo: &mut HashMap<NodeId, NodeId>,
    ) -> Result<NodeId, ZddError> {
        let level = self.level(f);
        if level > target {
            return Ok(f);
        }
        self.stats.cache_lookups += 1;
        if let Some(&r) = memo.get(&f) {
            self.stats.cache_hits += 1;
            return Ok(r);
        }
        let (hi, lo) = self.branches(f);
        let r = if level == target {
            let p = self.mul(h, hi)?;
            self.xor(p, lo)?
        } else {
            let hi = self.substitute_rec(hi, target, h, memo)?;
            let lo = self.substitute_rec(lo, target, h, memo)?;
            // `h` may reintroduce this level or one above it, so build with a product, not `mk`.
            let x = self.mk(level, ONE, ZERO)?;
            let p = self.mul(x, hi)?;
            self.xor(p, lo)?
        };
        if memo.len() + self.cache.len() >= self.budget.max_cache_entries {
            return Err(ZddError::CacheBudgetExceeded {
                limit: self.budget.max_cache_entries,
            });
        }
        memo.insert(f, r);
        Ok(r)
    }

    /// The diagram of `f`, built by splitting its terms on the top variable.
    pub fn from_anf(&mut self, f: &Anf) -> Result<NodeId, ZddError> {
        let terms: Vec<Vec<u32>> = f
            .terms()
            .map(|t| {
                let mut levels: Vec<u32> = t.vars().map(|v| self.order.level_of(v)).collect();
                levels.sort_unstable();
                levels
            })
            .collect();
        self.build(terms.iter().map(Vec::as_slice).collect())
    }

    /// The sum of `terms`, each a strictly ascending list of levels.
    fn build(&mut self, terms: Vec<&[u32]>) -> Result<NodeId, ZddError> {
        let mut constant = false;
        let mut rest = Vec::with_capacity(terms.len());
        for t in terms {
            if t.is_empty() {
                constant = !constant;
            } else {
                rest.push(t);
            }
        }
        let Some(top) = rest.iter().map(|t| t[0]).min() else {
            return Ok(constant as NodeId);
        };
        let (with, mut without): (Vec<&[u32]>, Vec<&[u32]>) =
            rest.into_iter().partition(|t| t[0] == top);
        let hi = self.build(with.into_iter().map(|t| &t[1..]).collect())?;
        if constant {
            without.push(&[]);
        }
        let lo = self.build(without)?;
        self.mk(top, hi, lo)
    }

    /// The terms of `f`, refused past `term_budget`.
    pub fn to_anf(&self, f: NodeId, term_budget: usize) -> Result<Anf, ZddError> {
        let mut out = Vec::new();
        let mut path = Vec::new();
        self.paths(f, &mut path, &mut out, term_budget)?;
        Ok(Anf::from_terms(out))
    }

    fn paths(
        &self,
        f: NodeId,
        path: &mut Vec<u32>,
        out: &mut Vec<Term>,
        budget: usize,
    ) -> Result<(), ZddError> {
        if f == ZERO {
            return Ok(());
        }
        if f == ONE {
            if out.len() >= budget {
                return Err(ZddError::TermBudgetExceeded { limit: budget });
            }
            out.push(Term::of(path));
            return Ok(());
        }
        let (hi, lo) = self.branches(f);
        path.push(self.order.var_at(self.level(f)));
        self.paths(hi, path, out, budget)?;
        path.pop();
        self.paths(lo, path, out, budget)
    }

    /// Distinct decision nodes reachable from `roots`: the shared size of those diagrams.
    pub fn reachable_nodes(&self, roots: &[NodeId]) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<NodeId> = roots.iter().copied().filter(|&r| r > ONE).collect();
        while let Some(f) = stack.pop() {
            if seen.insert(f) {
                let (hi, lo) = self.branches(f);
                stack.extend([hi, lo].into_iter().filter(|&c| c > ONE));
            }
        }
        seen.len()
    }

    /// The number of terms of `f`, i.e. its expanded ANF size, without expanding it.
    pub fn term_count(&self, f: NodeId) -> u128 {
        fn count(z: &Zdd, f: NodeId, memo: &mut HashMap<NodeId, u128>) -> u128 {
            if f <= ONE {
                return f as u128;
            }
            if let Some(&c) = memo.get(&f) {
                return c;
            }
            let (hi, lo) = z.branches(f);
            let c = count(z, hi, memo).saturating_add(count(z, lo, memo));
            memo.insert(f, c);
            c
        }
        count(self, f, &mut HashMap::new())
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use super::*;
    use crate::boolean::anf::AnfWork;

    const BIG: usize = 1 << 20;
    const ROOMY: Budget = Budget {
        max_nodes: 1 << 20,
        max_cache_entries: 1 << 22,
    };

    fn random_anf(rng: &mut StdRng, n: u32, terms: usize) -> Anf {
        Anf::from_terms((0..terms).map(|_| {
            let vars: Vec<u32> = (0..n).filter(|_| rng.gen_bool(0.3)).collect();
            Term::of(&vars)
        }))
    }

    fn scrambled(rng: &mut StdRng, n: u32) -> VariableOrder {
        let mut vars: Vec<u32> = (0..n).collect();
        for i in (1..vars.len()).rev() {
            vars.swap(i, rng.gen_range(0..=i));
        }
        VariableOrder::new(vars).unwrap()
    }

    #[test]
    fn anf_round_trips_through_the_diagram() {
        let mut rng = StdRng::seed_from_u64(1168);
        for _ in 0..50 {
            let mut z = Zdd::new(scrambled(&mut rng, 9), ROOMY);
            let f = random_anf(&mut rng, 9, 40);
            let root = z.from_anf(&f).unwrap();
            assert_eq!(z.to_anf(root, BIG).unwrap(), f);
            assert_eq!(z.term_count(root), f.len() as u128);
        }
    }

    #[test]
    fn equal_polynomials_share_a_root() {
        let mut rng = StdRng::seed_from_u64(7);
        let mut z = Zdd::new(VariableOrder::identity(8), ROOMY);
        let f = random_anf(&mut rng, 8, 30);
        let g = random_anf(&mut rng, 8, 30);
        let (a, b) = (z.from_anf(&f).unwrap(), z.from_anf(&g).unwrap());
        let ab = z.xor(a, b).unwrap();
        let ba_built = z.from_anf(&g.add(&f)).unwrap();
        assert_eq!(ab, ba_built);
    }

    #[test]
    fn boolean_identities_hold() {
        let mut rng = StdRng::seed_from_u64(11);
        let mut z = Zdd::new(scrambled(&mut rng, 8), ROOMY);
        for _ in 0..30 {
            let [f, g, h] = [0, 1, 2].map(|_| {
                let a = random_anf(&mut rng, 8, 12);
                z.from_anf(&a).unwrap()
            });
            assert_eq!(z.mul(f, f).unwrap(), f, "f·f = f");
            assert_eq!(z.xor(f, f).unwrap(), ZERO, "f + f = 0");
            let gh = z.xor(g, h).unwrap();
            let left = z.mul(f, gh).unwrap();
            let (fg, fh) = (z.mul(f, g).unwrap(), z.mul(f, h).unwrap());
            assert_eq!(left, z.xor(fg, fh).unwrap(), "f·(g + h) = f·g + f·h");
        }
    }

    #[test]
    fn operations_agree_with_the_anf_oracle() {
        let mut rng = StdRng::seed_from_u64(12);
        for _ in 0..30 {
            let mut z = Zdd::new(scrambled(&mut rng, 10), ROOMY);
            let (f, g) = (random_anf(&mut rng, 10, 15), random_anf(&mut rng, 10, 15));
            let h = random_anf(&mut rng, 10, 4);
            let (a, b, c) = (
                z.from_anf(&f).unwrap(),
                z.from_anf(&g).unwrap(),
                z.from_anf(&h).unwrap(),
            );
            let mut work = AnfWork::default();
            let p = z.mul(a, b).unwrap();
            assert_eq!(
                z.to_anf(p, BIG).unwrap(),
                f.mul(&g, BIG, &mut work).unwrap()
            );
            let v = rng.gen_range(0..10);
            let s = z.substitute(a, v, c).unwrap();
            assert_eq!(
                z.to_anf(s, BIG).unwrap(),
                f.substitute(v, &h, BIG, &mut work).unwrap()
            );
        }
    }

    #[test]
    fn exceeding_the_node_budget_is_refused() {
        let budget = Budget {
            max_nodes: 5,
            max_cache_entries: 1 << 10,
        };
        let mut z = Zdd::new(VariableOrder::identity(16), budget);
        let f = Anf::from_terms((0..16).map(|v| Term::of(&[v])));
        assert_eq!(
            z.from_anf(&f),
            Err(ZddError::NodeBudgetExceeded { limit: 5 })
        );
    }

    #[test]
    fn exceeding_the_cache_budget_is_refused() {
        let budget = Budget {
            max_nodes: 1 << 10,
            max_cache_entries: 2,
        };
        let mut z = Zdd::new(VariableOrder::identity(16), budget);
        let f = z
            .from_anf(&Anf::from_terms((0..8).map(|v| Term::of(&[v]))))
            .unwrap();
        let g = z
            .from_anf(&Anf::from_terms((8..16).map(|v| Term::of(&[v]))))
            .unwrap();
        assert_eq!(z.mul(f, g), Err(ZddError::CacheBudgetExceeded { limit: 2 }));
    }
}
