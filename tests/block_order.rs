use zeebra::{BlockOrder, BlockOrderKind, Monomial, MonomialOrder};

// Invalid block boundaries cannot construct an order, and the order remains a compact Copy value.
#[test]
fn checked_blocks_and_identity() {
    use BlockOrderKind::*;
    assert!(BlockOrder::checked(0, 0, Lexicographic, Lexicographic).is_err());
    assert!(BlockOrder::checked(3, 0, Lexicographic, Lexicographic).is_err());
    assert!(BlockOrder::checked(3, 3, Lexicographic, Lexicographic).is_err());
    assert!(BlockOrder::checked(3, 4, Lexicographic, Lexicographic).is_err());
    #[cfg(target_pointer_width = "64")]
    assert!(BlockOrder::checked(u32::MAX as usize + 1, 1, Lexicographic, Lexicographic).is_err());
    let block = BlockOrder::checked(3, 1, Lexicographic, GradedReverseLexicographic).unwrap();
    let order = MonomialOrder::Block(block);
    assert_eq!(order, MonomialOrder::Block(block));
    assert_eq!(order.arity(), Some(3));
    #[cfg(target_pointer_width = "64")]
    assert_eq!(
        std::mem::size_of::<MonomialOrder>(),
        2 * std::mem::size_of::<usize>()
    );
}

// Every supported block pair is a multiplicative total order with prefix elimination dominance.
#[test]
fn block_order_laws() {
    use BlockOrderKind::*;
    let kinds = [
        Lexicographic,
        GradedLexicographic,
        GradedReverseLexicographic,
    ];
    let monomials: Vec<_> = (0..27)
        .map(|i| Monomial::<3>::new(&[i / 9, i / 3 % 3, i % 3]))
        .collect();
    for first in kinds {
        for second in kinds {
            for split in [1, 2] {
                let order =
                    MonomialOrder::Block(BlockOrder::checked(3, split, first, second).unwrap());
                let mut suffix_only = [u32::MAX; 3];
                suffix_only[..split].fill(0);
                assert!(order
                    .cmp(
                        &Monomial::<3>::new(&[1, 0, 0]),
                        &Monomial::<3>::new(&suffix_only)
                    )
                    .is_gt());
                for a in &monomials {
                    for b in &monomials {
                        let cmp = order.cmp(a, b);
                        assert_eq!(cmp.is_eq(), a == b);
                        assert_eq!(cmp, order.cmp(b, a).reverse());
                        for c in &monomials {
                            assert_eq!(cmp, order.cmp(&(a * c), &(b * c)));
                            if cmp.is_le() && order.cmp(b, c).is_le() {
                                assert!(order.cmp(a, c).is_le());
                            }
                        }
                    }
                }
            }
        }
    }
}

use zeebra::{
    fields::Zp32003,
    grobner::{f4, f4::F4Error},
    MultivariatePolynomial,
};
type Poly = MultivariatePolynomial<3, Zp32003>;
fn parse(s: &str) -> Poly {
    Poly::parse(s, ["x", "y", "z"]).unwrap()
}
fn block(prefix: BlockOrderKind, suffix: BlockOrderKind) -> MonomialOrder {
    MonomialOrder::Block(BlockOrder::checked(3, 1, prefix, suffix).unwrap())
}
fn kinds() -> [BlockOrderKind; 3] {
    use BlockOrderKind::*;
    [
        Lexicographic,
        GradedLexicographic,
        GradedReverseLexicographic,
    ]
}
fn same_basis(mut actual: Vec<Poly>, mut expected: Vec<Poly>, order: MonomialOrder) {
    actual.sort_by(|a, b| order.cmp(&a.leading_monomial(order), &b.leading_monomial(order)));
    expected.sort_by(|a, b| order.cmp(&a.leading_monomial(order), &b.leading_monomial(order)));
    assert_eq!(actual, expected);
}

// F4 checks the ring arity before inspecting even empty, zero, or unit input.
#[test]
fn f4_rejects_arity_before_comparison() {
    let wrong = MonomialOrder::Block(BlockOrder::checked(4, 1, kinds()[0], kinds()[0]).unwrap());
    for input in [
        vec![],
        vec![parse("0")],
        vec![parse("1")],
        vec![parse("x+y")],
    ] {
        assert!(matches!(
            f4(&input, wrong),
            Err(F4Error::InvalidOptions { .. })
        ));
    }
}

// Direct comparisons reject arity mismatch rather than truncating a block.
#[test]
#[should_panic(expected = "block order arity mismatch")]
fn comparison_rejects_arity() {
    let order = block(kinds()[0], kinds()[0]);
    order.cmp(&Monomial::<2>::one(), &Monomial::<2>::one());
}

// F4 gives the independently derived elimination ideal in both dimensions and handles zero/unit ideals.
#[test]
fn f4_elimination_reference_bases() {
    for first in kinds() {
        for second in kinds() {
            let order = block(first, second);
            let input = [parse("x-y^2"), parse("x*z-1")];
            let basis = f4(&input, order).unwrap();
            same_basis(basis.clone(), vec![parse("x-y^2"), parse("y^2*z-1")], order);
            let retained: Vec<_> = basis
                .into_iter()
                .filter(|p| p.terms().iter().all(|(m, _)| m.exponents()[0] == 0))
                .collect();
            assert_eq!(retained, vec![parse("y^2*z-1")]);
            same_basis(
                f4(
                    &[input[0].clone(), input[1].clone(), parse("z^2-z-1")],
                    order,
                )
                .unwrap(),
                vec![parse("x-z+1"), parse("y^2-z+1"), parse("z^2-z-1")],
                order,
            );
            assert!(f4::<3, Zp32003>(&[], order).unwrap().is_empty());
            same_basis(
                f4(&[parse("0"), parse("1")], order).unwrap(),
                vec![parse("1")],
                order,
            );
        }
    }
}

// Graded blocks compare degrees beyond u32::MAX without wrapping.
#[test]
fn wide_block_degrees() {
    for kind in [
        BlockOrderKind::GradedLexicographic,
        BlockOrderKind::GradedReverseLexicographic,
    ] {
        let order = MonomialOrder::Block(BlockOrder::checked(3, 2, kind, kind).unwrap());
        assert!(order
            .cmp(
                &Monomial::<3>::new(&[u32::MAX, 1, 0]),
                &Monomial::<3>::new(&[u32::MAX, 0, 0])
            )
            .is_gt());
    }
}

// Every boundary and suborder contributes to the canonical order tag and instance digest.
#[cfg(feature = "external-runners")]
#[test]
fn canonical_order_identity() {
    use zeebra::grobner::external::{order_from_tag, order_tag, FieldSpec, Instance};
    let mut tags = std::collections::HashSet::new();
    let mut digests = std::collections::HashSet::new();
    for split in [1, 2] {
        for prefix in kinds() {
            for suffix in kinds() {
                let order =
                    MonomialOrder::Block(BlockOrder::checked(3, split, prefix, suffix).unwrap());
                let tag = order_tag(order);
                assert_eq!(order_from_tag(&tag), Some(order));
                assert!(tags.insert(tag.into_owned()));
                let instance = Instance::new(
                    "block",
                    "test",
                    FieldSpec::prime(32003),
                    vec!["x".into(), "y".into(), "z".into()],
                    vec!["x-y^2".into()],
                    order,
                );
                assert!(digests.insert(instance.digest()));
                assert!(
                    zeebra::grobner::external::contract::order_is_unsupported_externally(order)
                );
            }
        }
    }
    for tag in [
        "block",
        "block:3:0:lex:lex",
        "block:3:3:lex:lex",
        "block:3:1:lex:weighted",
        "block:3:1:lex:lex:extra",
        "block:3:1:lex",
        "block:0:0:lex:lex",
    ] {
        assert_eq!(order_from_tag(tag), None);
    }
}

// The shape certificate refuses block orders because their product grading is not total degree.
#[test]
fn shape_certificate_refuses_block_grading() {
    use zeebra::grobner::{f4::F4Options, shape_position_hypotheses, HypothesisGap};
    let order = block(kinds()[1], kinds()[2]);
    assert!(matches!(
        shape_position_hypotheses(
            &[parse("x"), parse("y"), parse("z")],
            order,
            &F4Options::default()
        ),
        Err(HypothesisGap::UngradedOrder { .. })
    ));
}

// Live Singular agrees coefficient-for-coefficient with every block pair, split, and dimension fixture.
#[test]
#[ignore = "requires Singular; run cargo test --test block_order live_singular -- --ignored"]
fn live_singular_product_order_oracle() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    let spelling = |kind| match kind {
        BlockOrderKind::Lexicographic => "lp",
        BlockOrderKind::GradedLexicographic => "Dp",
        BlockOrderKind::GradedReverseLexicographic => "dp",
    };
    for split in [1, 2] {
        for first in kinds() {
            for second in kinds() {
                let order =
                    MonomialOrder::Block(BlockOrder::checked(3, split, first, second).unwrap());
                for system in ["x-y^2,x*z-1", "x-y^2,x*z-1,z^2-z-1", "0", "1"] {
                    let script = format!("ring r=32003,(x,y,z),({}({split}),{}({})); short=0; option(redSB); ideal i={system}; ideal g=std(i); int k; for(k=1;k<=size(g);k++){{print(\"@poly \"+string(g[k]));}} print(\"@done\"); quit;", spelling(first), spelling(second), 3-split);
                    let mut child = Command::new("timeout")
                        .args(["10s", "Singular", "-q"])
                        .stdin(Stdio::piped())
                        .stdout(Stdio::piped())
                        .stderr(Stdio::piped())
                        .spawn()
                        .expect("Singular and timeout must be installed");
                    child
                        .stdin
                        .take()
                        .unwrap()
                        .write_all(script.as_bytes())
                        .unwrap();
                    let output = child.wait_with_output().unwrap();
                    let text = String::from_utf8(output.stdout).unwrap();
                    assert!(
                        output.status.success() && text.contains("@done") && !text.contains('?'),
                        "{text}"
                    );
                    let expected = text
                        .lines()
                        .filter_map(|line| line.strip_prefix("@poly "))
                        .map(parse)
                        .collect();
                    let input: Vec<_> = system.split(',').map(parse).collect();
                    same_basis(f4(&input, order).unwrap(), expected, order);
                }
            }
        }
    }
}

// Two lex blocks reproduce full lex, and the same zero-dimensional reference survives built-in controls.
#[test]
fn built_in_order_controls() {
    let order = block(BlockOrderKind::Lexicographic, BlockOrderKind::Lexicographic);
    let monomials: Vec<_> = (0..27)
        .map(|i| Monomial::<3>::new(&[i / 9, i / 3 % 3, i % 3]))
        .collect();
    for a in &monomials {
        for b in &monomials {
            assert_eq!(order.cmp(a, b), MonomialOrder::Lexicographic.cmp(a, b));
        }
    }
    let input = [parse("x-y^2"), parse("x*z-1"), parse("z^2-z-1")];
    for control in [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ] {
        same_basis(
            f4(&input, control).unwrap(),
            vec![parse("x-z+1"), parse("y^2-z+1"), parse("z^2-z-1")],
            control,
        );
    }
}

// All subprocess adapters refuse unsupported block orders without probing or launching their binaries.
#[cfg(feature = "external-runners")]
#[test]
fn subprocess_adapters_refuse_block_orders() {
    use std::time::Duration;
    use zeebra::grobner::{
        differential::SingularOracle,
        external::{
            grobx, sylvester, ExternalSolver, FieldSpec, GrobxSolver, GroebnerJlSolver,
            GroebnerRsSolver, Instance, MsolveSolver, SagebrushSolver, SingularSolver, Support,
            SylvesterSolver, Task, Unsupported,
        },
    };
    let scratch =
        std::env::temp_dir().join(format!("zeebra-block-adapters-{}", std::process::id()));
    let singular = SingularSolver::new(
        SingularOracle::new("missing-Singular", &scratch, Duration::from_secs(1), false).unwrap(),
    );
    let julia = GroebnerJlSolver::new("missing-julia", None, &scratch).unwrap();
    let sagebrush = SagebrushSolver::new("missing-sagebrush", &scratch).unwrap();
    let msolve = MsolveSolver::new("missing-msolve", &scratch);
    let groebner = GroebnerRsSolver::new("missing-groebner", &scratch).unwrap();
    let grobx = GrobxSolver::new("missing-grobx", &scratch, grobx::Mode::Raw).unwrap();
    let sylvester =
        SylvesterSolver::new("missing-sylvester", &scratch, sylvester::Mode::Raw).unwrap();
    let input = Instance::new(
        "blocks",
        "test",
        FieldSpec::prime(32003),
        vec!["x".into(), "y".into(), "z".into()],
        vec!["x-y^2".into()],
        block(kinds()[0], kinds()[2]),
    );
    let solvers: [&dyn ExternalSolver; 7] = [
        &singular, &julia, &sagebrush, &msolve, &groebner, &grobx, &sylvester,
    ];
    for solver in solvers {
        assert!(matches!(
            solver.supports(&input, Task::ReducedGrobnerBasis),
            Support::No(Unsupported::Order { .. })
        ));
    }
    std::fs::remove_dir_all(scratch).unwrap();
}

// The default interreduction policy keeps unmeasured block orders on division while Matrix stays explicit.
#[test]
fn block_interreduction_is_conservative() {
    use zeebra::grobner::f4::InterreductionRoute;
    let order = block(kinds()[0], kinds()[2]);
    assert!(!InterreductionRoute::ByOrder.builds_a_matrix(order));
    assert!(InterreductionRoute::Matrix.builds_a_matrix(order));
}
