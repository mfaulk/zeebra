// Reads an msolve-format system and prints the degrevlex Groebner basis computed by
// Sagebrush's `sagebrush_mpoly::f4::groebner_p`. The input format is deliberately msolve's,
// so one smoke-test file drives both tools.

use sagebrush_bigint::BigInt;
use sagebrush_mpoly::order::{Order, Packing};
use sagebrush_mpoly::{Coeffs, QPoly, ZPoly};

/// A term as an exponent vector plus a coefficient, before packing.
struct Term {
    exps: Vec<u64>,
    coeff: i64,
}

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

/// Renders a monomial word as `x^2*y`, or `1` for the constant monomial.
fn monomial(w: u64, pk: &Packing, vars: &[String]) -> String {
    let mask = pk.mask();
    let mut parts: Vec<String> = Vec::new();
    for (i, v) in vars.iter().enumerate() {
        let e = (w >> pk.shift(i)) & mask;
        if e == 1 {
            parts.push(v.clone());
        } else if e > 1 {
            parts.push(format!("{v}^{e}"));
        }
    }
    if parts.is_empty() {
        "1".to_string()
    } else {
        parts.join("*")
    }
}

/// The leading monomial word under `o`. Sagebrush keeps terms in decreasing **lex** order of
/// the packed word whatever the monomial order is, so for degrevlex the leading term is not
/// the first one and has to be found with `Packing::key`.
fn leading_word(f: &QPoly, o: Order) -> Option<u64> {
    let pk = Packing { n: f.num.n, bits: f.num.bits };
    f.num.exps.iter().copied().max_by_key(|&w| pk.key(o, w))
}

/// Renders a polynomial with its terms in decreasing `o`-order, so the leading term is first
/// and the text lines up with msolve's, Singular's and Groebner.jl's.
fn render(f: &QPoly, vars: &[String], o: Order) -> String {
    let pk = Packing { n: f.num.n, bits: f.num.bits };
    let cs: Vec<i64> = match &f.num.coeffs {
        Coeffs::Small(v) => v.clone(),
        Coeffs::Big(v) => v.iter().map(|b| format!("{b}").parse().unwrap_or(0)).collect(),
    };
    let mut terms: Vec<(u64, i64)> = f.num.exps.iter().copied().zip(cs).collect();
    terms.sort_by_key(|&(w, _)| std::cmp::Reverse(pk.key(o, w)));
    let out: Vec<String> = terms
        .iter()
        .map(|&(w, c)| {
            let m = monomial(w, &pk, vars);
            if m == "1" { format!("{c}") } else { format!("{c}*{m}") }
        })
        .collect();
    if out.is_empty() {
        "0".into()
    } else {
        out.join(" + ")
    }
}

fn main() -> Result<(), String> {
    let path = std::env::args().nth(1).ok_or("usage: sagebrush-gb-driver <file.ms>")?;
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

    let o = Order::DegRevLex;
    let t0 = std::time::Instant::now();
    let mut g = sagebrush_mpoly::f4::groebner_p(&sys, o, p)?;
    let secs = t0.elapsed().as_secs_f64();

    // Sort by increasing leading monomial, which is how msolve and Singular print a basis.
    g.sort_by_key(|f| {
        let pk = Packing { n: f.num.n, bits: f.num.bits };
        leading_word(f, o).map(|w| pk.key(o, w)).unwrap_or(0)
    });

    println!("#engine:               sagebrush-mpoly f4::groebner_p");
    println!("#field characteristic: {p}");
    println!("#variable order:       {}", vars.join(", "));
    println!("#monomial order:       degrevlex (Order::DegRevLex)");
    println!("#length of basis:      {} elements sorted by increasing leading monomials", g.len());
    println!("#seconds:              {secs:.6}");
    for f in &g {
        println!("{}", render(f, &vars, o));
    }
    println!("--- leading monomials ---");
    for f in &g {
        let pk = Packing { n: f.num.n, bits: f.num.bits };
        match leading_word(f, o) {
            Some(w) => println!("{}", monomial(w, &pk, &vars)),
            None => println!("0"),
        }
    }
    Ok(())
}
