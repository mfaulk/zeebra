//! The Boolean normal form under verified triangular rules, by the ZDD and by expanded ANF.
//!
//! Rules `x_i + h_i` whose tails mention only variables after their heads form a lexicographic
//! Boolean Gröbner basis together with the field equations (Dagstuhl 10271, Thm. 3.1), so the
//! reduced normal form is unique and both routes must return it exactly. The rules are checked
//! for that shape before either route sees them.

use super::anf::{Anf, AnfWork};
use super::zdd::{Budget, NodeId, Op, Zdd, ONE};
use super::{RuleError, VariableOrder, ZddError};

/// The rule `x_head + tail`, i.e. `x_head ← tail`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rule {
    /// The variable being defined.
    pub head: u32,
    /// Its definition.
    pub tail: Anf,
}

/// Rules checked to be triangular in an order: distinct heads, every tail variable after its head.
#[derive(Clone, Debug)]
pub struct TriangularRules {
    order: VariableOrder,
    rules: Vec<Rule>,
}

impl TriangularRules {
    /// Checks `rules` against `order`.
    pub fn verify(order: VariableOrder, mut rules: Vec<Rule>) -> Result<Self, RuleError> {
        let n = order.len() as u32;
        let mut seen = vec![false; n as usize];
        for rule in &rules {
            if rule.head >= n {
                return Err(RuleError::VariableOutOfRange { var: rule.head });
            }
            if std::mem::replace(&mut seen[rule.head as usize], true) {
                return Err(RuleError::DuplicateHead { head: rule.head });
            }
            let head_level = order.level_of(rule.head);
            for v in rule.tail.terms().flat_map(|t| t.vars()) {
                if v >= n {
                    return Err(RuleError::VariableOutOfRange { var: v });
                }
                if order.level_of(v) <= head_level {
                    return Err(RuleError::NotTriangular {
                        head: rule.head,
                        var: v,
                    });
                }
            }
        }
        rules.sort_by_key(|r| order.level_of(r.head));
        Ok(Self { order, rules })
    }

    /// The order the rules were verified in.
    pub fn order(&self) -> &VariableOrder {
        &self.order
    }

    /// The rules, by head from the top of the order.
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    /// Extends an assignment of the free variables to one that satisfies every rule.
    pub fn complete(&self, free: impl Fn(u32) -> bool) -> Vec<bool> {
        let mut values: Vec<bool> = (0..self.order.len() as u32).map(free).collect();
        // A tail only reads variables below its head, so evaluate from the bottom up.
        for rule in self.rules.iter().rev() {
            values[rule.head as usize] = rule.tail.evaluate(|v| values[v as usize]);
        }
        values
    }
}

/// The expanded-ANF route: substitute each head into `f`, from the top of the order down.
///
/// A tail only mentions variables below its head, so a head once substituted never comes back
/// and one pass suffices.
pub fn anf_normal_form(
    rules: &TriangularRules,
    f: &Anf,
    term_budget: usize,
    work: &mut AnfWork,
) -> Result<Anf, ZddError> {
    let mut f = f.clone();
    for rule in rules.rules() {
        if f.mentions(rule.head) {
            f = f.substitute(rule.head, &rule.tail, term_budget, work)?;
        }
    }
    Ok(f)
}

impl Zdd {
    /// A manager over the rules' order holding their tails, ready for [`Zdd::normal_form`].
    pub fn with_rules(rules: &TriangularRules, budget: Budget) -> Result<Self, ZddError> {
        let mut z = Zdd::new(rules.order().clone(), budget);
        for rule in rules.rules() {
            let tail = z.from_anf(&rule.tail)?;
            let level = z.order().level_of(rule.head) as usize;
            z.tails[level] = Some(tail);
        }
        Ok(z)
    }

    /// The normal form of `f` modulo the installed rules and the field equations.
    ///
    /// Dagstuhl 10271 Alg. 1 (llnf) with the rules indexed by level rather than encoded in a
    /// diagram: with `x` at `f`'s top, `f = x·f1 + f0`, and the result is `x·nf(f1) + nf(f0)`
    /// when `x` is free and `nf(h)·nf(f1) + nf(f0)` when a rule defines `x ← h`. Every recursive
    /// result lies below `x`, so the free case is a single node.
    pub fn normal_form(&mut self, f: NodeId) -> Result<NodeId, ZddError> {
        if f <= ONE {
            return Ok(f);
        }
        if let Some(r) = self.cached((Op::NormalForm, f, 0)) {
            return Ok(r);
        }
        let level = self.level(f);
        let (hi, lo) = self.branches(f);
        let t = self.normal_form(hi)?;
        let e = self.normal_form(lo)?;
        let r = match self.tails[level as usize] {
            None => self.mk(level, t, e)?,
            Some(h) => {
                let h = self.normal_form(h)?;
                let p = self.mul(h, t)?;
                self.xor(p, e)?
            }
        };
        self.remember((Op::NormalForm, f, 0), r)?;
        Ok(r)
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use super::*;
    use crate::boolean::anf::Term;
    use crate::fields::Zp2;
    use crate::{Monomial, MonomialOrder, MultivariatePolynomial, One};

    const BIG: usize = 1 << 20;
    const ROOMY: Budget = Budget {
        max_nodes: 1 << 20,
        max_cache_entries: 1 << 22,
    };

    fn random_anf(rng: &mut StdRng, vars: &[u32], terms: usize) -> Anf {
        Anf::from_terms((0..terms).map(|_| {
            let picked: Vec<u32> = vars
                .iter()
                .copied()
                .filter(|_| rng.gen_bool(0.35))
                .collect();
            Term::of(&picked)
        }))
    }

    /// A random order, random heads, and tails over the variables below each head.
    fn random_system(rng: &mut StdRng, n: u32, heads: usize) -> TriangularRules {
        let mut vars: Vec<u32> = (0..n).collect();
        for i in (1..vars.len()).rev() {
            vars.swap(i, rng.gen_range(0..=i));
        }
        let mut levels: Vec<usize> = (0..n as usize - 1).collect();
        for i in (1..levels.len()).rev() {
            levels.swap(i, rng.gen_range(0..=i));
        }
        let rules = levels[..heads]
            .iter()
            .map(|&l| {
                let terms = rng.gen_range(1..5);
                Rule {
                    head: vars[l],
                    tail: random_anf(rng, &vars[l + 1..], terms),
                }
            })
            .collect();
        TriangularRules::verify(VariableOrder::new(vars).unwrap(), rules).unwrap()
    }

    fn zdd_nf(rules: &TriangularRules, f: &Anf) -> Anf {
        let mut z = Zdd::with_rules(rules, ROOMY).unwrap();
        let root = z.from_anf(f).unwrap();
        let nf = z.normal_form(root).unwrap();
        z.to_anf(nf, BIG).unwrap()
    }

    #[test]
    fn a_tail_mentioning_its_head_or_above_is_refused() {
        let order = VariableOrder::identity(3);
        let rule = |head, vars: &[u32]| Rule {
            head,
            tail: Anf::from_terms([Term::of(vars)]),
        };
        let refused = |rules| TriangularRules::verify(order.clone(), rules).unwrap_err();
        assert_eq!(
            refused(vec![rule(1, &[0])]),
            RuleError::NotTriangular { head: 1, var: 0 }
        );
        assert_eq!(
            refused(vec![rule(1, &[1, 2])]),
            RuleError::NotTriangular { head: 1, var: 1 }
        );
        assert_eq!(
            refused(vec![rule(0, &[1]), rule(0, &[2])]),
            RuleError::DuplicateHead { head: 0 }
        );
        assert_eq!(
            refused(vec![rule(0, &[5])]),
            RuleError::VariableOutOfRange { var: 5 }
        );
        // The same rule is triangular in an order that puts its head first.
        let flipped = VariableOrder::new(vec![1, 0, 2]).unwrap();
        assert!(TriangularRules::verify(flipped, vec![rule(1, &[0])]).is_ok());
    }

    #[test]
    fn the_routes_agree_and_the_result_is_reduced_and_idempotent() {
        let mut rng = StdRng::seed_from_u64(1168);
        for _ in 0..60 {
            let rules = random_system(&mut rng, 10, 5);
            let all: Vec<u32> = (0..10).collect();
            let f = random_anf(&mut rng, &all, 8);
            let expected = anf_normal_form(&rules, &f, BIG, &mut AnfWork::default()).unwrap();
            let mut z = Zdd::with_rules(&rules, ROOMY).unwrap();
            let root = z.from_anf(&f).unwrap();
            let nf = z.normal_form(root).unwrap();
            assert_eq!(z.to_anf(nf, BIG).unwrap(), expected);
            assert_eq!(z.normal_form(nf).unwrap(), nf, "NF(NF(f)) = NF(f)");
            for rule in rules.rules() {
                assert!(!expected.mentions(rule.head), "x{} survives", rule.head);
            }
        }
    }

    /// On every point of the variety the rules cut out, `f` and its normal form agree.
    #[test]
    fn the_normal_form_agrees_with_f_on_every_satisfying_assignment() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let rules = random_system(&mut rng, 9, 4);
            let all: Vec<u32> = (0..9).collect();
            let f = random_anf(&mut rng, &all, 10);
            let nf = zdd_nf(&rules, &f);
            for bits in 0u32..1 << 9 {
                let point = rules.complete(|v| bits >> v & 1 == 1);
                let at = |v: u32| point[v as usize];
                assert_eq!(f.evaluate(at), nf.evaluate(at), "assignment {bits:09b}");
            }
        }
    }

    const N: usize = 10;

    /// `f` as an ordinary GF(2) polynomial with variable `x_v` at exponent slot `level_of(v)`, so
    /// that the crate's lex order (slot 0 largest) is the diagram's order.
    fn to_poly(order: &VariableOrder, f: &Anf) -> MultivariatePolynomial<N, Zp2> {
        let terms: Vec<_> = f
            .terms()
            .map(|t| {
                let mut e = [0u32; N];
                for v in t.vars() {
                    e[order.level_of(v) as usize] = 1;
                }
                (Monomial::new(&e), Zp2::one())
            })
            .collect();
        MultivariatePolynomial::new(&terms)
    }

    #[test]
    fn the_normal_form_matches_ordinary_reduction_with_field_equations() {
        let mut rng = StdRng::seed_from_u64(9);
        for _ in 0..25 {
            let rules = random_system(&mut rng, N as u32, 5);
            let order = rules.order();
            let mut divisors: Vec<_> = rules
                .rules()
                .iter()
                .map(|r| to_poly(order, &r.tail.add(&Anf::var(r.head))))
                .collect();
            divisors.extend((0..N).map(|slot| {
                MultivariatePolynomial::new(&[
                    (Monomial::univariate(slot, 2), Zp2::one()),
                    (Monomial::univariate(slot, 1), Zp2::one()),
                ])
            }));
            let all: Vec<u32> = (0..N as u32).collect();
            let f = random_anf(&mut rng, &all, 6);
            let ordinary = to_poly(order, &f).normal_form(&divisors, MonomialOrder::Lexicographic);
            assert_eq!(ordinary, to_poly(order, &zdd_nf(&rules, &f)));
        }
    }

    /// `x^2 + x + 1` generates the unit ideal of the Boolean quotient and a proper ideal of GF(2)[x].
    #[test]
    fn x_squared_plus_x_plus_one_is_a_unit_only_in_the_boolean_quotient() {
        assert_eq!(Anf::from_exponents(&[&[2], &[1], &[0]]), Anf::one());

        let g: MultivariatePolynomial<1, Zp2> = MultivariatePolynomial::new(&[
            (Monomial::new(&[2]), Zp2::one()),
            (Monomial::new(&[1]), Zp2::one()),
            (Monomial::new(&[0]), Zp2::one()),
        ]);
        let one = MultivariatePolynomial::new(&[(Monomial::new(&[0]), Zp2::one())]);
        // One generator is its own Gröbner basis, so a nonzero remainder of 1 means 1 ∉ <g>.
        assert_eq!(one.normal_form(&[g], MonomialOrder::Lexicographic), one);
        let univariate = crate::UnivariatePolynomial::new(&[Zp2::one(), Zp2::one(), Zp2::one()]);
        assert!(crate::is_irreducible(&univariate));
    }
}
