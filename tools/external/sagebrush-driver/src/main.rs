// Reads an msolve-format system and prints the Groebner basis Sagebrush computes for it. The
// input format is deliberately msolve's, so one smoke-test file drives both tools.
//
// Two axes are selectable, because Sagebrush's engine has both and a benchmark that cannot ask
// for the second route cannot compare the two: `--order` picks the monomial order and `--route`
// picks `f4::groebner_p` (direct, any order) or `fglm::groebner_fglm` (order conversion from a
// degrevlex basis, lex target, p < 2^31). Both default to the original behaviour — degrevlex by
// F4 — so an invocation with no flags is what it always was.

use std::collections::{HashSet, VecDeque};

use sagebrush_bigint::BigInt;
use sagebrush_mpoly::order::{Order, Packing};
use sagebrush_mpoly::{Coeffs, QPoly, ZPoly};

/// A term as an exponent vector plus a coefficient, before packing.
struct Term {
    exps: Vec<u64>,
    coeff: i64,
}

/// A result polynomial: terms as an exponent vector and a coefficient in `[0, p)`, by decreasing
/// monomial under the requested order.
///
/// Exponent vectors rather than packed words because the FGLM route's output is not packable —
/// `engine/mpoly/src/fglm.rs:16` notes that a target basis can carry degrees "far beyond the
/// packed words", so packing one back would silently truncate it.
type Poly = Vec<(Vec<u64>, i64)>;

/// Parses one polynomial: a sum of signed monomials such as `-3*x^2*y + z - 1`.
fn parse_poly(src: &str, vars: &[String], p: u64) -> Result<Vec<Term>, String> {
    let n = vars.len();
    let mut terms: Vec<Term> = Vec::new();
    // Split into signed chunks without losing the sign.
    let mut chunks: Vec<(i64, String)> = Vec::new();
    let mut sign: i64 = 1;
    let mut cur = String::new();
    for ch in src.chars().filter(|c| !c.is_whitespace()) {
        match ch {
            '+' | '-' if !cur.is_empty() => {
                chunks.push((sign, std::mem::take(&mut cur)));
                sign = if ch == '-' { -1 } else { 1 };
            }
            '+' => {}
            '-' => sign = -sign,
            _ => cur.push(ch),
        }
    }
    if !cur.is_empty() {
        chunks.push((sign, cur));
    }

    for (sg, chunk) in chunks {
        let mut exps = vec![0u64; n];
        let mut coeff: i64 = 1;
        for factor in chunk.split('*') {
            if factor.is_empty() {
                continue;
            }
            let (base, exp) = match factor.split_once('^') {
                Some((b, e)) => (b, e.parse::<u64>().map_err(|e| e.to_string())?),
                None => (factor, 1u64),
            };
            match vars.iter().position(|v| v == base) {
                Some(i) => exps[i] += exp,
                None => {
                    // A numeric factor; integer literals only.
                    let v: i64 = base
                        .parse()
                        .map_err(|_| format!("not a variable or integer: {base:?}"))?;
                    let mut acc: i64 = 1;
                    for _ in 0..exp {
                        acc = ((acc as i128 * v as i128) % p as i128) as i64;
                    }
                    coeff = ((coeff as i128 * acc as i128) % p as i128) as i64;
                }
            }
        }
        let c = (sg * coeff).rem_euclid(p as i64);
        if c != 0 {
            terms.push(Term { exps, coeff: c });
        }
    }
    Ok(terms)
}

/// Packs terms into a `QPoly`. Sagebrush packs the first variable in the highest bit field
/// (`engine/mpoly/src/order.rs`, `Packing::shift`) and keeps terms in decreasing lex order.
fn to_qpoly(terms: &[Term], n: usize, bits: u32, p: u64) -> QPoly {
    let pk = Packing { n, bits };
    let mut packed: Vec<(u64, i64)> = terms
        .iter()
        .map(|t| {
            let mut w = 0u64;
            for (i, &e) in t.exps.iter().enumerate() {
                w |= e << pk.shift(i);
            }
            (w, t.coeff)
        })
        .collect();
    packed.sort_by(|a, b| b.0.cmp(&a.0));
    QPoly {
        num: ZPoly {
            n,
            bits,
            exps: packed.iter().map(|x| x.0).collect(),
            coeffs: Coeffs::Small(packed.iter().map(|x| x.1).collect()),
        },
        den: BigInt::from(1i64),
        p,
    }
}

/// The comparison key of an exponent vector: lexicographically bigger for the bigger monomial.
///
/// A second implementation of the engine's `Packing::key`, needed because that one takes a packed
/// word and the FGLM route's exponents do not pack (see [`Poly`]). The two must agree, and
/// `test_the_exponent_key_agrees_with_the_engines_packed_key` asserts they do on every order over
/// packable words — this being exactly the function whose first version got degrevlex wrong.
fn order_key(o: Order, e: &[u64]) -> Vec<u64> {
    let degree: u64 = e.iter().sum();
    match o {
        Order::Lex => e.to_vec(),
        Order::DegLex => std::iter::once(degree).chain(e.iter().copied()).collect(),
        // Degree first, then the *smaller* last exponent wins, which is the complement-and-reverse
        // the engine builds into the low half of its key.
        Order::DegRevLex => std::iter::once(degree)
            .chain(e.iter().rev().map(|&x| u64::MAX - x))
            .collect(),
        Order::InvLex => e.iter().rev().copied().collect(),
    }
}

/// Renders an exponent vector as `x^2*y`, or `1` for the constant monomial.
fn monomial(e: &[u64], vars: &[String]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (i, v) in vars.iter().enumerate() {
        match e.get(i).copied().unwrap_or(0) {
            0 => {}
            1 => parts.push(v.clone()),
            k => parts.push(format!("{v}^{k}")),
        }
    }
    if parts.is_empty() {
        "1".to_string()
    } else {
        parts.join("*")
    }
}

/// Renders a polynomial with its terms in decreasing order, so the leading term is first and the
/// text lines up with msolve's, Singular's and Groebner.jl's.
fn render(f: &Poly, vars: &[String]) -> String {
    if f.is_empty() {
        return "0".into();
    }
    f.iter()
        .map(|(e, c)| {
            let m = monomial(e, vars);
            if m == "1" {
                format!("{c}")
            } else {
                format!("{c}*{m}")
            }
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

/// A `QPoly` from `f4::groebner_p` as a [`Poly`].
///
/// Sagebrush keeps a polynomial's terms in decreasing **lex** order of the packed word whatever
/// the monomial order is (`groebner_p` sorts on the raw word), so for every order but lex the
/// first stored term is *not* the leading one — the sort here is what makes it so, and taking
/// `exps[0]` instead yields a plausible-looking and entirely wrong leading monomial.
fn from_qpoly(f: &QPoly, o: Order) -> Poly {
    let pk = Packing {
        n: f.num.n,
        bits: f.num.bits,
    };
    let coeffs: Vec<i64> = match &f.num.coeffs {
        Coeffs::Small(v) => v.clone(),
        Coeffs::Big(v) => v.iter().map(|b| format!("{b}").parse().unwrap_or(0)).collect(),
    };
    let mut terms: Poly = f
        .num
        .exps
        .iter()
        .copied()
        .zip(coeffs)
        .map(|(w, c)| (pk.unpack(w), c))
        .collect();
    terms.sort_by_key(|(e, _)| std::cmp::Reverse(order_key(o, e)));
    terms
}

/// A `QEP` from `fglm::groebner_fglm` as a [`Poly`].
///
/// Over `GF(p)` every coefficient is an integer residue carried in a `BigRational` with
/// denominator one (`fglm.rs:336`); a denominator other than one would mean the rational route ran
/// and is an error rather than something to round away. Converted through the decimal text because
/// this crate deliberately takes no dependency of its own on the big-integer stack.
fn from_qep(f: &[(Vec<u32>, sagebrush_bigint::BigRational)], o: Order) -> Result<Poly, String> {
    let mut terms: Poly = Vec::with_capacity(f.len());
    for (exps, coeff) in f {
        let denominator = coeff.denom().to_string();
        if denominator != "1" {
            return Err(format!("FGLM returned the non-integer coefficient {coeff}"));
        }
        let numerator: i64 = coeff
            .numer()
            .to_string()
            .parse()
            .map_err(|_| format!("FGLM returned the out-of-range coefficient {coeff}"))?;
        terms.push((exps.iter().map(|&x| x as u64).collect(), numerator));
    }
    terms.sort_by_key(|(e, _)| std::cmp::Reverse(order_key(o, e)));
    Ok(terms)
}

/// How many standard monomials [`quotient_dimension`] will enumerate before giving up.
///
/// A ceiling and not a limit of the mathematics: the walk is finite whenever the ideal is
/// zero-dimensional, but "finite" can still be larger than is worth the memory, and an adapter
/// reading no dimension is in exactly the position it was in before the driver reported one.
const STAIRCASE_CAP: usize = 1 << 18;

/// [`quotient_dimension`] for an ideal that is not zero-dimensional. Singular's `vdim` reports a
/// positive-dimensional ideal the same way, so an adapter reading both sees one convention.
const NOT_ZERO_DIMENSIONAL: i64 = -1;

/// [`quotient_dimension`] for a staircase abandoned at [`STAIRCASE_CAP`]. Distinct from
/// [`NOT_ZERO_DIMENSIONAL`] so that a log says which of the two happened, though an adapter treats
/// both as "not reported".
const STAIRCASE_ABANDONED: i64 = -2;

/// `dim_k k[x]/I` as the number of standard monomials under `leads`.
///
/// **The driver's own computation, not Sagebrush's.** `fglm_p` computes the same number as
/// `stair.len()` (`engine/mpoly/src/fglm.rs:97`) and exposes only the boolean `zero_dimensional`,
/// so there is nothing to read out; counting the monomials no leading monomial divides is the
/// definition, and being an independent computation it is a genuine third invariant to check a
/// comparand against rather than a restatement of one of the other two.
///
/// Order-independent in value: the count is the quotient dimension whichever order `leads` came
/// from.
fn quotient_dimension(leads: &[Vec<u64>], n: usize) -> i64 {
    if n == 0 {
        return NOT_ZERO_DIMENSIONAL;
    }
    // The unit ideal: 1 is a leading monomial, so the quotient ring is zero.
    if leads.iter().any(|l| l.iter().all(|&e| e == 0)) {
        return 0;
    }
    // Zero-dimensional exactly when every variable has a pure power among the leading monomials.
    // Checked before walking because without it the walk does not terminate.
    let finite = (0..n).all(|i| {
        leads.iter().any(|l| {
            l.get(i).copied().unwrap_or(0) > 0
                && l.iter().enumerate().all(|(j, &e)| j == i || e == 0)
        })
    });
    if !finite {
        return NOT_ZERO_DIMENSIONAL;
    }

    let divided = |m: &[u64]| {
        leads
            .iter()
            .any(|l| l.iter().zip(m).all(|(a, b)| a <= b))
    };
    let mut seen: HashSet<Vec<u64>> = HashSet::new();
    let mut queue: VecDeque<Vec<u64>> = VecDeque::new();
    let one = vec![0u64; n];
    seen.insert(one.clone());
    queue.push_back(one);
    let mut count = 0usize;
    while let Some(m) = queue.pop_front() {
        count += 1;
        if count > STAIRCASE_CAP {
            return STAIRCASE_ABANDONED;
        }
        for i in 0..n {
            let mut next = m.clone();
            next[i] += 1;
            if divided(&next) {
                continue;
            }
            if seen.insert(next.clone()) {
                queue.push_back(next);
            }
        }
    }
    count as i64
}

/// Which Sagebrush entry point computes the basis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Route {
    /// `f4::groebner_p`, directly in the requested order.
    F4,
    /// `fglm::groebner_fglm`, by conversion from a degrevlex basis.
    Fglm,
}

impl Route {
    fn parse(s: &str) -> Option<Route> {
        match s {
            "f4" => Some(Route::F4),
            "fglm" => Some(Route::Fglm),
            _ => None,
        }
    }

    /// The `#engine:` value: the function actually called, so the echo names the route.
    fn engine(self) -> &'static str {
        match self {
            Route::F4 => "sagebrush-mpoly f4::groebner_p",
            Route::Fglm => "sagebrush-mpoly fglm::groebner_fglm",
        }
    }

    fn tag(self) -> &'static str {
        match self {
            Route::F4 => "f4 (direct)",
            Route::Fglm => "fglm (order conversion from degrevlex)",
        }
    }
}

/// The largest modulus the FGLM route accepts.
///
/// `fglm.rs:329` returns `Ok(None)` for `p >= 1 << 31` — the **same** value it returns for an ideal
/// that is not zero-dimensional. The driver therefore has to refuse an out-of-range modulus itself,
/// because past this bound "no answer" stops meaning anything in particular. Eight times narrower
/// than the `[2, 2^62)` the basis route accepts.
const FGLM_MAX_CHARACTERISTIC: u64 = 1 << 31;

/// The order's name in Sagebrush's own vocabulary, which is what the header echoes.
fn order_tag(o: Order) -> &'static str {
    match o {
        Order::Lex => "lex",
        Order::DegLex => "deglex",
        Order::DegRevLex => "degrevlex",
        Order::InvLex => "invlex",
    }
}

fn order_variant(o: Order) -> &'static str {
    match o {
        Order::Lex => "Order::Lex",
        Order::DegLex => "Order::DegLex",
        Order::DegRevLex => "Order::DegRevLex",
        Order::InvLex => "Order::InvLex",
    }
}

const USAGE: &str =
    "usage: sagebrush-gb-driver <file.ms> [--order lex|deglex|degrevlex|invlex] [--route f4|fglm]";

/// The command line: the input path, the order and the route.
///
/// Strict about unknown flags. A driver that ignored one would answer a question other than the
/// one asked and say nothing about it, which is the whole class of defect the echoed headers exist
/// to catch.
fn arguments(argv: &[String]) -> Result<(String, Order, Route), String> {
    let mut path: Option<String> = None;
    let mut order = Order::DegRevLex;
    let mut route = Route::F4;
    let mut rest = argv.iter();
    while let Some(argument) = rest.next() {
        match argument.as_str() {
            "--order" => {
                let value = rest.next().ok_or_else(|| format!("--order needs a value\n{USAGE}"))?;
                order = Order::parse(value)
                    .ok_or_else(|| format!("unknown order {value:?}\n{USAGE}"))?;
            }
            "--route" => {
                let value = rest.next().ok_or_else(|| format!("--route needs a value\n{USAGE}"))?;
                route = Route::parse(value)
                    .ok_or_else(|| format!("unknown route {value:?}\n{USAGE}"))?;
            }
            flag if flag.starts_with('-') => return Err(format!("unknown flag {flag:?}\n{USAGE}")),
            positional if path.is_none() => path = Some(positional.to_string()),
            extra => return Err(format!("unexpected argument {extra:?}\n{USAGE}")),
        }
    }
    let path = path.ok_or_else(|| USAGE.to_string())?;
    if route == Route::Fglm && !matches!(order, Order::Lex | Order::InvLex) {
        // `groebner_fglm` documents lex and invlex as its targets; a degree order would be the
        // source basis it starts from, so asking for one is asking for no conversion at all.
        return Err(format!(
            "the fglm route converts to lex or invlex, not to {}",
            order_tag(order)
        ));
    }
    Ok((path, order, route))
}

fn main() -> Result<(), String> {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let (path, o, route) = arguments(&argv)?;
    let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
    let mut lines = text.lines().filter(|l| !l.trim().is_empty());

    let vars: Vec<String> = lines
        .next()
        .ok_or("missing variable line")?
        .split(',')
        .map(|s| s.trim().to_string())
        .collect();
    let p: u64 = lines
        .next()
        .ok_or("missing characteristic line")?
        .trim()
        .parse()
        .map_err(|e: std::num::ParseIntError| e.to_string())?;
    if p == 0 {
        return Err("this driver handles prime fields only".into());
    }
    if route == Route::Fglm && p >= FGLM_MAX_CHARACTERISTIC {
        return Err(format!(
            "the fglm route needs p < {FGLM_MAX_CHARACTERISTIC}, and p is {p}"
        ));
    }
    let n = vars.len();

    // Generators are one per line, comma-separated as in msolve's format.
    let body: String = lines.collect::<Vec<_>>().join("");
    let parsed: Vec<Vec<Term>> = body
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| parse_poly(s, &vars, p))
        .collect::<Result<_, _>>()?;

    let bits = (64 / n) as u32;
    let sys: Vec<QPoly> = parsed.iter().map(|t| to_qpoly(t, n, bits, p)).collect();

    let t0 = std::time::Instant::now();
    let mut g: Vec<Poly> = match route {
        Route::F4 => sagebrush_mpoly::f4::groebner_p(&sys, o, p)?
            .iter()
            .map(|f| from_qpoly(f, o))
            .collect(),
        Route::Fglm => {
            // `None` here can only be the zero-dimensionality condition: the modulus was checked
            // against `FGLM_MAX_CHARACTERISTIC` above, which is the other way it arises.
            let converted = sagebrush_mpoly::fglm::groebner_fglm(&sys, o, p, false)?
                .ok_or("the ideal is not zero-dimensional, so FGLM does not apply")?;
            converted
                .iter()
                .map(|f| from_qep(f, o))
                .collect::<Result<_, _>>()?
        }
    };
    let secs = t0.elapsed().as_secs_f64();

    // Sort by increasing leading monomial, which is how msolve and Singular print a basis.
    g.sort_by_key(|f| f.first().map(|(e, _)| order_key(o, e)).unwrap_or_default());

    let leads: Vec<Vec<u64>> = g
        .iter()
        .map(|f| f.first().map(|(e, _)| e.clone()).unwrap_or_else(|| vec![0; n]))
        .collect();

    println!("#engine:               {}", route.engine());
    println!("#field characteristic: {p}");
    println!("#variable order:       {}", vars.join(", "));
    println!(
        "#monomial order:       {} ({})",
        order_tag(o),
        order_variant(o)
    );
    println!("#route:                {}", route.tag());
    println!(
        "#quotient dimension:   {}",
        quotient_dimension(&leads, n)
    );
    println!(
        "#length of basis:      {} elements sorted by increasing leading monomials",
        g.len()
    );
    println!("#seconds:              {secs:.6}");
    for f in &g {
        println!("{}", render(f, &vars));
    }
    println!("--- leading monomials ---");
    for e in &leads {
        println!("{}", monomial(e, &vars));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const ORDERS: [Order; 4] = [Order::Lex, Order::DegLex, Order::DegRevLex, Order::InvLex];

    /// The exponent-vector order key ranks monomials exactly as the engine's packed key does.
    ///
    /// The one test that matters most here: `order_key` is a second implementation of
    /// `Packing::key`, and a degrevlex key that is subtly wrong produces a well-formed basis with
    /// the wrong leading monomials.
    #[test]
    fn test_the_exponent_key_agrees_with_the_engines_packed_key() {
        let pk = Packing { n: 4, bits: 8 };
        // Every exponent vector in [0, 5)^4, which is 625 monomials and 195 000 ordered pairs.
        let monomials: Vec<Vec<u64>> = (0..5u64)
            .flat_map(|a| {
                (0..5u64).flat_map(move |b| {
                    (0..5u64).flat_map(move |c| (0..5u64).map(move |d| vec![a, b, c, d]))
                })
            })
            .collect();
        for o in ORDERS {
            for left in &monomials {
                for right in &monomials {
                    let packed = pk.key(o, pk.pack(left)).cmp(&pk.key(o, pk.pack(right)));
                    let ours = order_key(o, left).cmp(&order_key(o, right));
                    assert_eq!(
                        packed,
                        ours,
                        "{:?} against {:?} under {}",
                        left,
                        right,
                        order_tag(o)
                    );
                }
            }
        }
    }

    /// A monomial renders from its exponent vector, with the constant monomial as `1`.
    #[test]
    fn test_a_monomial_renders_from_its_exponent_vector() {
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        assert_eq!(monomial(&[0, 0, 0], &vars), "1");
        assert_eq!(monomial(&[2, 1, 0], &vars), "x^2*y");
        assert_eq!(monomial(&[0, 0, 4], &vars), "z^4");
    }

    /// A polynomial renders with explicit coefficients and the leading term first.
    #[test]
    fn test_a_polynomial_renders_with_explicit_coefficients() {
        let vars = vec!["x".to_string(), "y".to_string()];
        let f: Poly = vec![(vec![2, 0], 1), (vec![0, 1], 3), (vec![0, 0], 65520)];
        assert_eq!(render(&f, &vars), "1*x^2 + 3*y + 65520");
        assert_eq!(render(&Vec::new(), &vars), "0");
    }

    /// The quotient dimension is the number of standard monomials under the leading monomials.
    #[test]
    fn test_the_quotient_dimension_counts_the_standard_monomials() {
        // <x^2, y^3> in k[x,y]: the standard monomials are x^i y^j for i < 2, j < 3.
        assert_eq!(quotient_dimension(&[vec![2, 0], vec![0, 3]], 2), 6);
        // <x, y>: only 1 is standard.
        assert_eq!(quotient_dimension(&[vec![1, 0], vec![0, 1]], 2), 1);
        // The leading monomials of `tools/external/smoke/system.ms`'s degrevlex basis. Two other
        // engines put the quotient dimension of that ideal at 12 independently of this walk:
        // `Singular`'s `vdim(std(I))`, and the Groebner.jl figure recorded in issue #341.
        let smoke = [
            vec![1, 1, 0],
            vec![2, 0, 0],
            vec![1, 0, 2],
            vec![0, 3, 0],
            vec![0, 0, 4],
            vec![0, 2, 2],
        ];
        assert_eq!(quotient_dimension(&smoke, 3), 12);
    }

    /// A positive-dimensional ideal is reported as such and never as a count.
    ///
    /// The walk over standard monomials does not terminate for one, so this is a precondition and
    /// not a presentation choice.
    #[test]
    fn test_a_positive_dimensional_ideal_has_no_quotient_dimension() {
        // <x*y> in k[x,y]: no pure power of either variable, so the staircase is infinite.
        assert_eq!(quotient_dimension(&[vec![1, 1]], 2), NOT_ZERO_DIMENSIONAL);
        // A pure power of x but not of y.
        assert_eq!(
            quotient_dimension(&[vec![2, 0], vec![1, 1]], 2),
            NOT_ZERO_DIMENSIONAL
        );
    }

    /// The unit ideal has quotient dimension zero rather than no dimension.
    #[test]
    fn test_the_unit_ideal_has_quotient_dimension_zero() {
        assert_eq!(quotient_dimension(&[vec![0, 0]], 2), 0);
    }

    /// An enumeration past the cap is abandoned rather than allowed to exhaust memory.
    #[test]
    fn test_an_oversized_staircase_is_abandoned_and_not_counted() {
        // <x^M, y^M> with M^2 standard monomials, chosen so M^2 exceeds the cap.
        let m = (STAIRCASE_CAP as f64).sqrt() as u64 + 2;
        assert_eq!(
            quotient_dimension(&[vec![m, 0], vec![0, m]], 2),
            STAIRCASE_ABANDONED
        );
    }

    /// The default command line is the original behaviour: degrevlex, by F4.
    #[test]
    fn test_the_default_command_line_is_degrevlex_by_f4() {
        let (path, order, route) = arguments(&["system.ms".to_string()]).expect("a bare path");
        assert_eq!(path, "system.ms");
        assert_eq!(order_tag(order), "degrevlex");
        assert!(route == Route::F4);
    }

    /// The order and the route are selectable, and are echoed by their Sagebrush names.
    #[test]
    fn test_the_order_and_route_are_selectable() {
        let (_, order, route) = arguments(&[
            "system.ms".to_string(),
            "--order".to_string(),
            "lex".to_string(),
            "--route".to_string(),
            "fglm".to_string(),
        ])
        .expect("lex by fglm");
        assert_eq!(order_tag(order), "lex");
        assert!(route == Route::Fglm);
    }

    /// An unknown flag, order or route is refused rather than ignored.
    #[test]
    fn test_an_unrecognized_argument_is_refused() {
        for argv in [
            vec!["system.ms".to_string(), "--jobs".to_string()],
            vec![
                "system.ms".to_string(),
                "--order".to_string(),
                "grevlex-ish".to_string(),
            ],
            vec![
                "system.ms".to_string(),
                "--route".to_string(),
                "buchberger".to_string(),
            ],
            vec!["system.ms".to_string(), "--order".to_string()],
            vec!["a.ms".to_string(), "b.ms".to_string()],
            vec![],
        ] {
            assert!(arguments(&argv).is_err(), "{:?}", argv);
        }
    }

    /// Asking FGLM for a degree order is refused: that is its source basis, not a conversion.
    #[test]
    fn test_the_fglm_route_refuses_a_degree_order_target() {
        let argv = vec![
            "system.ms".to_string(),
            "--order".to_string(),
            "degrevlex".to_string(),
            "--route".to_string(),
            "fglm".to_string(),
        ];
        let error = arguments(&argv).expect_err("degrevlex is not an FGLM target");
        assert!(error.contains("degrevlex"), "{}", error);
    }

    /// A `QPoly` is read in decreasing order of the requested order, not of the packed word.
    ///
    /// The trap this driver exists to avoid: `groebner_p` stores terms by decreasing packed word,
    /// which is decreasing lex, so under degrevlex the first stored term is not the leading one.
    #[test]
    fn test_a_qpoly_is_reordered_from_stored_lex_order_to_the_requested_order() {
        let n = 3;
        let bits = 8;
        // x*z + z^4, stored lex-first as x*z then z^4; under degrevlex z^4 leads on degree.
        let terms = [
            Term {
                exps: vec![1, 0, 1],
                coeff: 1,
            },
            Term {
                exps: vec![0, 0, 4],
                coeff: 1,
            },
        ];
        let f = to_qpoly(&terms, n, bits, 65521);
        let pk = Packing { n, bits };
        assert_eq!(
            pk.unpack(f.num.exps[0]),
            vec![1, 0, 1],
            "stored by decreasing packed word, so x*z is first"
        );
        assert_eq!(from_qpoly(&f, Order::DegRevLex)[0].0, vec![0, 0, 4]);
        assert_eq!(from_qpoly(&f, Order::Lex)[0].0, vec![1, 0, 1]);
    }
}
