//! Public, generic fixtures: structured circuit families, their scrambled orders, a dense control.
//!
//! Every structured instance is a circuit: inputs, and signals defined by a rule over signals
//! created before them. Reversing creation order puts each signal above everything it reads, so it
//! is a topological order and the rules are triangular in it (the Dagstuhl 10271 §4 condition).
//! A scrambled order is a uniformly random choice at each step of the same topological sort, so it
//! keeps the rules triangular while moving every variable, inputs included.

use rand::{rngs::StdRng, Rng, SeedableRng};

use super::anf::{Anf, Term};
use super::normal_form::{Rule, TriangularRules};
use super::VariableOrder;

/// One fixture: rules, the polynomials to normalize, and its natural order.
#[derive(Clone, Debug)]
pub struct Instance {
    /// A label with the family and size.
    pub name: String,
    /// The definitions.
    pub rules: Vec<Rule>,
    /// The polynomials to normalize.
    pub targets: Vec<Anf>,
    /// Reverse creation order.
    pub natural: VariableOrder,
}

impl Instance {
    /// The rules verified in the natural order.
    pub fn natural_rules(&self) -> TriangularRules {
        TriangularRules::verify(self.natural.clone(), self.rules.clone())
            .expect("a circuit is triangular in reverse creation order")
    }

    /// The rules verified in a seeded random topological order.
    pub fn scrambled_rules(&self, seed: u64) -> TriangularRules {
        let n = self.natural.len();
        // `x_head` must precede every variable its tail reads.
        let mut blockers = vec![0usize; n];
        let mut reads: Vec<Vec<u32>> = vec![Vec::new(); n];
        for rule in &self.rules {
            let mut vars: Vec<u32> = rule.tail.terms().flat_map(|t| t.vars()).collect();
            vars.sort_unstable();
            vars.dedup();
            for v in &vars {
                blockers[*v as usize] += 1;
            }
            reads[rule.head as usize] = vars;
        }
        let mut ready: Vec<u32> = (0..n as u32)
            .filter(|&v| blockers[v as usize] == 0)
            .collect();
        let mut rng = StdRng::seed_from_u64(seed);
        let mut order = Vec::with_capacity(n);
        while !ready.is_empty() {
            let v = ready.swap_remove(rng.gen_range(0..ready.len()));
            order.push(v);
            for &w in &reads[v as usize] {
                blockers[w as usize] -= 1;
                if blockers[w as usize] == 0 {
                    ready.push(w);
                }
            }
        }
        let order = VariableOrder::new(order).expect("a topological sort is a permutation");
        TriangularRules::verify(order, self.rules.clone()).expect("topological, so triangular")
    }
}

/// Builds an instance signal by signal.
#[derive(Default)]
struct Circuit {
    rules: Vec<Rule>,
    next: u32,
}

impl Circuit {
    fn input(&mut self) -> u32 {
        self.next += 1;
        self.next - 1
    }

    fn define(&mut self, tail: Anf) -> u32 {
        let head = self.input();
        self.rules.push(Rule { head, tail });
        head
    }

    fn finish(self, name: String, targets: Vec<Anf>) -> Instance {
        let natural = VariableOrder::new((0..self.next).rev().collect()).expect("a permutation");
        Instance {
            name,
            rules: self.rules,
            targets,
            natural,
        }
    }
}

fn sum(vars: &[u32]) -> Anf {
    Anf::from_terms(vars.iter().map(|&v| Term::of(&[v])))
}

fn poly(terms: &[&[u32]]) -> Anf {
    Anf::from_terms(terms.iter().map(|t| Term::of(t)))
}

/// An `n`-bit ripple-carry adder; the targets are the sum bits and the carry out.
pub fn adder(n: usize) -> Instance {
    let mut c = Circuit::default();
    let mut outputs = Vec::new();
    let mut carry: Option<u32> = None;
    for _ in 0..n {
        let (a, b) = (c.input(), c.input());
        let (s, next) = match carry {
            None => (c.define(sum(&[a, b])), c.define(poly(&[&[a, b]]))),
            Some(k) => (
                c.define(sum(&[a, b, k])),
                c.define(poly(&[&[a, b], &[a, k], &[b, k]])),
            ),
        };
        outputs.push(s);
        carry = Some(next);
    }
    outputs.extend(carry);
    let targets = outputs.into_iter().map(Anf::var).collect();
    c.finish(format!("adder-{n}"), targets)
}

/// An AND/XOR ladder `t_i = (t_{i-1} + a_i)·(b_i + c_i)`; the target is `t_n`.
pub fn ladder(n: usize) -> Instance {
    let mut c = Circuit::default();
    let mut t = c.input();
    for _ in 0..n {
        let (a, b, d) = (c.input(), c.input(), c.input());
        t = c.define(poly(&[&[t, b], &[t, d], &[a, b], &[a, d]]));
    }
    c.finish(format!("ladder-{n}"), vec![Anf::var(t)])
}

/// A toy SPN of width `w`: per round a chi layer `y_j = x_j + (x_{j+1} + 1)·x_{j+2}`, then the
/// rotation-XOR mix `z_j = y_j + y_{j+1} + y_{j+3}` (indices mod `w`). Targets: the final state.
pub fn chi_spn(w: usize, rounds: usize) -> Instance {
    let mut c = Circuit::default();
    let mut state: Vec<u32> = (0..w).map(|_| c.input()).collect();
    for _ in 0..rounds {
        let y: Vec<u32> = (0..w)
            .map(|j| {
                let (x0, x1, x2) = (state[j], state[(j + 1) % w], state[(j + 2) % w]);
                c.define(poly(&[&[x0], &[x1, x2], &[x2]]))
            })
            .collect();
        state = (0..w)
            .map(|j| c.define(sum(&[y[j], y[(j + 1) % w], y[(j + 3) % w]])))
            .collect();
    }
    let targets = state.into_iter().map(Anf::var).collect();
    c.finish(format!("chi-{w}x{rounds}"), targets)
}

/// Dense random MQ, the adverse control: `k` inputs, `k` signals `y_j = q_j(x)` with each `q_j`
/// a uniformly random quadratic, and a target that is a uniformly random quadratic in the `y_j`.
pub fn dense_mq(k: usize, seed: u64) -> Instance {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut quadratic = |vars: &[u32]| {
        let mut terms = vec![Term::ONE];
        for (i, &a) in vars.iter().enumerate() {
            terms.push(Term::of(&[a]));
            terms.extend(vars[i + 1..].iter().map(|&b| Term::of(&[a, b])));
        }
        Anf::from_terms(terms.into_iter().filter(|_| rng.gen_bool(0.5)))
    };
    let mut c = Circuit::default();
    let x: Vec<u32> = (0..k).map(|_| c.input()).collect();
    let y: Vec<u32> = (0..k).map(|_| c.define(quadratic(&x))).collect();
    let target = quadratic(&y);
    c.finish(format!("mq-{k}-s{seed}"), vec![target])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean::anf::AnfWork;
    use crate::boolean::normal_form::anf_normal_form;
    use crate::boolean::zdd::{Budget, Zdd};

    const BUDGET: Budget = Budget {
        max_nodes: 1 << 20,
        max_cache_entries: 1 << 22,
    };

    /// The adder adds: on every input pair its normal forms evaluate to `a + b`.
    #[test]
    fn the_adder_fixture_adds() {
        let n = 3;
        let inst = adder(n);
        let rules = inst.natural_rules();
        let mut z = Zdd::with_rules(&rules, BUDGET).unwrap();
        let nfs: Vec<Anf> = inst
            .targets
            .iter()
            .map(|t| {
                let root = z.from_anf(t).unwrap();
                let nf = z.normal_form(root).unwrap();
                z.to_anf(nf, 1 << 20).unwrap()
            })
            .collect();
        for a in 0u32..1 << n {
            for b in 0u32..1 << n {
                // Inputs a_i, b_i are variables 4i and 4i + 1 (each bit also defines s_i, c_i).
                let at = |v: u32| {
                    let (bit, slot) = (v / 4, v % 4);
                    (if slot == 0 { a } else { b }) >> bit & 1 == 1
                };
                let got: u32 = nfs
                    .iter()
                    .enumerate()
                    .map(|(i, f)| (f.evaluate(at) as u32) << i)
                    .sum();
                assert_eq!(got, a + b);
            }
        }
    }

    #[test]
    fn every_family_and_scramble_agrees_with_the_anf_route() {
        let instances = [adder(4), ladder(5), chi_spn(4, 2), dense_mq(5, 3)];
        for inst in &instances {
            for rules in [
                inst.natural_rules(),
                inst.scrambled_rules(1),
                inst.scrambled_rules(2),
            ] {
                let mut z = Zdd::with_rules(&rules, BUDGET).unwrap();
                for t in &inst.targets {
                    let expected = anf_normal_form(&rules, t, 1 << 20, &mut AnfWork::default());
                    let root = z.from_anf(t).unwrap();
                    let nf = z.normal_form(root).unwrap();
                    assert_eq!(
                        z.to_anf(nf, 1 << 20).unwrap(),
                        expected.unwrap(),
                        "{}",
                        inst.name
                    );
                }
            }
        }
    }

    #[test]
    fn scrambling_moves_inputs_and_signals() {
        let inst = ladder(6);
        let scrambled = inst.scrambled_rules(5);
        assert_ne!(scrambled.order(), &inst.natural);
    }
}
