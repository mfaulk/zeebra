//! A tour of the public API, in the order a new user needs it.
//!
//! ```text
//! cargo run --release --example quickstart
//! ```

use rand::{prelude::StdRng, SeedableRng};
use zeebra::{
    fields::{Bn254Fr, Zp2147483647},
    grobner::{f4, f4_with_options, solve, F4Error, F4Options},
    FiniteField, MonomialOrder, MultivariatePolynomial, Polynomial, UnivariatePolynomial,
};

type F = Zp2147483647;

fn main() {
    // 1. Field elements: a 31-bit prime field and the 254-bit BN254 scalar field, same trait.
    let a = F::new(3);
    let b = F::new(5);
    println!("in GF(2^31 - 1): 3 * 5 = {}, 3 / 5 = {}", a * b, a / b);
    let x = Bn254Fr::new(7);
    println!("in BN254's Fr:   7^-1 * 7 = {}", x.inverse() * x);

    // 2. Polynomial arithmetic: univariate product and evaluation, and multivariate parsing.
    let p = UnivariatePolynomial::new(&[F::new(1), F::new(1)]); // 1 + t
    let q = &p * &p; // 1 + 2t + t^2
    println!("(1 + t)^2 at t = 4: {}", q.eval(&F::new(4)));
    let vars = ["x", "y"];
    let f = MultivariatePolynomial::<2, F>::parse("x^2 + y - 3", vars).unwrap();
    let g = MultivariatePolynomial::<2, F>::parse("x - y + 1", vars).unwrap();
    println!("f * g has {} terms", (&f * &g).terms().len());

    // 3. A Gröbner basis by F4.
    let basis = f4(
        &[f.clone(), g.clone()],
        MonomialOrder::GradedReverseLexicographic,
    )
    .unwrap();
    println!("the reduced grevlex basis has {} elements", basis.len());

    // 4. Every solution in the field, each verified against the original equations.
    let mut rng = StdRng::seed_from_u64(0);
    for point in solve(&[f.clone(), g.clone()], &mut rng) {
        println!("solution: x = {}, y = {}", point[0], point[1]);
    }

    // 5. Explicit resource limits: a budget that is crossed is a typed error, never a hang.
    let katsura_like = [
        "x^2 + 2*y^2 + 2*z^2 - x",
        "2*x*y + 2*y*z - y",
        "x + 2*y + 2*z - 1",
    ]
    .map(|text| MultivariatePolynomial::<3, F>::parse(text, ["x", "y", "z"]).unwrap());
    let tight = F4Options {
        max_matrix_rows: 2,
        ..F4Options::default()
    };
    match f4_with_options(
        &katsura_like,
        MonomialOrder::GradedReverseLexicographic,
        &tight,
    ) {
        Err(F4Error::TooManyRows { limit }) => println!("refused: more than {limit} matrix rows"),
        other => println!("unexpected: {other:?}"),
    }
}
