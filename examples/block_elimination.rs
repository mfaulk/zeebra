use zeebra::{
    fields::Zp32003, grobner::f4, BlockOrder, BlockOrderKind, MonomialOrder, MultivariatePolynomial,
};

fn main() {
    let vars = ["x", "y", "z"];
    let system = ["x-y^2", "x*z-1"]
        .map(|text| MultivariatePolynomial::<3, Zp32003>::parse(text, vars).unwrap());
    let blocks = BlockOrder::checked(
        3,
        1,
        BlockOrderKind::Lexicographic,
        BlockOrderKind::GradedReverseLexicographic,
    )
    .unwrap();
    let basis = f4(&system, MonomialOrder::Block(blocks)).unwrap();
    let retained: Vec<_> = basis
        .iter()
        .filter(|p| {
            p.terms()
                .iter()
                .all(|(m, _)| m.exponents()[..blocks.split()].iter().all(|&e| e == 0))
        })
        .collect();
    let expected = MultivariatePolynomial::<3, Zp32003>::parse("y^2*z-1", vars).unwrap();
    assert_eq!(retained, vec![&expected]);
    for polynomial in retained {
        println!("{polynomial}");
    }
}
