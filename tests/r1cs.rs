use std::time::Duration;
use zeebra::{
    fields::{Bn254Fr, Gf256, Zp7},
    r1cs::{Error, ImportLimits, R1cs, WireRole},
    FiniteField, One, Zero,
};

type Row = [Vec<(u32, u64)>; 3];

fn encode(wires: u32, rows: &[Row]) -> Vec<u8> {
    let mut header = 8u32.to_le_bytes().to_vec();
    header.extend(7u64.to_le_bytes());
    for count in [
        wires,
        u32::from(wires > 1),
        u32::from(wires > 2),
        u32::from(wires > 3),
    ] {
        header.extend(count.to_le_bytes());
    }
    header.extend(u64::from(wires).to_le_bytes());
    header.extend((rows.len() as u32).to_le_bytes());
    let mut constraints = Vec::new();
    for row in rows {
        for lc in row {
            constraints.extend((lc.len() as u32).to_le_bytes());
            for (wire, coefficient) in lc {
                constraints.extend(wire.to_le_bytes());
                constraints.extend(coefficient.to_le_bytes());
            }
        }
    }
    let mapping = (0..u64::from(wires)).flat_map(u64::to_le_bytes).collect();
    container(&[(1, header), (2, constraints), (3, mapping)])
}

fn container(parts: &[(u32, Vec<u8>)]) -> Vec<u8> {
    let mut output = b"r1cs".to_vec();
    output.extend(1u32.to_le_bytes());
    output.extend((parts.len() as u32).to_le_bytes());
    for (kind, data) in parts {
        output.extend(kind.to_le_bytes());
        output.extend((data.len() as u64).to_le_bytes());
        output.extend(data);
    }
    output
}

fn parts(bytes: &[u8]) -> Vec<(u32, Vec<u8>)> {
    let count = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    let mut at = 12;
    (0..count)
        .map(|_| {
            let kind = u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
            let len = u64::from_le_bytes(bytes[at + 4..at + 12].try_into().unwrap()) as usize;
            at += 12;
            let data = bytes[at..at + len].to_vec();
            at += len;
            (kind, data)
        })
        .collect()
}

fn fixture() -> Vec<u8> {
    encode(
        4,
        &[
            [
                vec![(0, 3), (1, 1), (2, 2)],
                vec![(2, 1), (3, 4)],
                vec![(0, 6), (3, 1)],
            ],
            [vec![(0, 1)], vec![(1, 1)], vec![(3, 1)]],
            [vec![], vec![(2, 1)], vec![]],
        ],
    )
}

/// The pinned Circom fixture retains BN254 modulus, row order, wire roles, labels and symbols.
#[test]
fn test_reads_the_pinned_circom_fixture() {
    let bytes = include_bytes!("fixtures/r1cs/multiplier.r1cs");
    let model = R1cs::<Bn254Fr>::parse(bytes, &ImportLimits::default())
        .unwrap()
        .with_symbols(include_str!("fixtures/r1cs/multiplier.sym"))
        .unwrap();
    assert_eq!(model.header().wire_count, 4);
    assert_eq!(model.header().constraint_count, 1);
    assert_eq!(model.constraints()[0].id, 0);
    assert_eq!(model.wire_labels(), &[0, 1, 2, 3]);
    assert_eq!(model.wire_role(0), Some(WireRole::Constant));
    assert_eq!(model.wire_role(1), Some(WireRole::PublicOutput));
    assert_eq!(model.wire_role(2), Some(WireRole::PublicInput));
    assert_eq!(model.wire_role(3), Some(WireRole::PrivateInput));
    assert_eq!(model.wire_role(4), None);
    assert_eq!(model.symbols()[1].name, "main.a");
    assert_eq!(
        model.source_digest(),
        "16ab9e569919f7d25f32321974db3b1803b469d4ab0c25769cc94cc3f0d324f7"
    );
    assert_eq!(
        model.canonical_digest(),
        "945ef7efeda20135be64cfb8a91533cad8aba99bf1cd8f56c5d55ded1b9c4add"
    );
    assert_eq!(model.constraints()[0].a.terms(), &[(2, -Bn254Fr::one())]);
    assert_eq!(model.constraints()[0].b.terms(), &[(3, Bn254Fr::one())]);
    assert_eq!(model.constraints()[0].c.terms(), &[(1, -Bn254Fr::one())]);
}

/// Wide canonical residues decode independently of the field's internal Montgomery representation.
#[test]
fn test_bn254_coefficients_are_canonical_little_endian_residues() {
    use rand::{rngs::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(725);
    let values = [
        Bn254Fr::new(255),
        Bn254Fr::new(256),
        Bn254Fr::new(600),
        -Bn254Fr::one(),
        Bn254Fr::random(&mut rng),
        Bn254Fr::random(&mut rng),
    ];
    for expected in values {
        let mut sections = parts(include_bytes!("fixtures/r1cs/multiplier.r1cs"));
        let constraints = &mut sections.iter_mut().find(|(kind, _)| *kind == 2).unwrap().1;
        let encoded: Vec<_> = expected
            .canonical_limbs()
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect();
        constraints[48..80].copy_from_slice(&encoded);
        let model =
            R1cs::<Bn254Fr>::parse(&container(&sections), &ImportLimits::default()).unwrap();
        assert_eq!(model.constraints()[0].b.terms(), &[(3, expected)]);
    }
}

/// Original sparse rows and expanded polynomials agree on every GF(7)^3 assignment.
#[test]
fn test_exhaustive_small_field_semantics() {
    let model = R1cs::<Zp7>::parse(&fixture(), &ImportLimits::default()).unwrap();
    let expansion = model.expand::<3>().unwrap();
    assert_eq!(expansion.row_ids, vec![0, 1, 2]);
    assert_eq!(expansion.variable_to_wire, vec![1, 2, 3]);
    assert_eq!(expansion.stats.products, 7);
    assert_eq!(expansion.stats.source_terms, 11);
    for a in 0..7 {
        for b in 0..7 {
            for c in 0..7 {
                let point = [Zp7::new(a), Zp7::new(b), Zp7::new(c)];
                let rows = model
                    .evaluate_assignment(&[Zp7::one(), point[0], point[1], point[2]])
                    .unwrap();
                let expanded: Vec<_> = expansion
                    .polynomials
                    .iter()
                    .map(|poly| poly.eval(&point))
                    .collect();
                assert_eq!(rows, expanded);
            }
        }
    }
}

/// Circom's independently generated witness is accepted and a changed public output is rejected.
#[test]
fn test_producer_witness_and_perturbation() {
    let model = R1cs::<Bn254Fr>::parse(
        include_bytes!("fixtures/r1cs/multiplier.r1cs"),
        &ImportLimits::default(),
    )
    .unwrap();
    let expansion = model.expand::<3>().unwrap();
    let mut wires = [
        Bn254Fr::one(),
        Bn254Fr::new(15),
        Bn254Fr::new(3),
        Bn254Fr::new(5),
    ];
    assert!(model
        .evaluate_assignment(&wires)
        .unwrap()
        .iter()
        .all(Zero::is_zero));
    assert!(expansion.polynomials[0].eval(&wires[1..]).is_zero());
    wires[1] += Bn254Fr::one();
    assert!(!model.evaluate_assignment(&wires).unwrap()[0].is_zero());
    assert_eq!(
        model.evaluate_assignment(&wires).unwrap()[0],
        expansion.polynomials[0].eval(&wires[1..])
    );
}

/// Section order does not change canonical identity or the polynomial system.
#[test]
fn test_canonical_roundtrip_and_section_order() {
    let bytes = fixture();
    let original = R1cs::<Zp7>::parse(&bytes, &ImportLimits::default()).unwrap();
    let mut reordered = parts(&bytes);
    reordered.reverse();
    let reordered = R1cs::<Zp7>::parse(&container(&reordered), &ImportLimits::default()).unwrap();
    assert_eq!(original.canonical_digest(), reordered.canonical_digest());
    assert_ne!(original.source_digest(), reordered.source_digest());
    let again = R1cs::<Zp7>::parse(&original.to_bytes(), &ImportLimits::default()).unwrap();
    assert_eq!(again.to_bytes(), bytes);
    assert_eq!(
        again.expand::<3>().unwrap().polynomials,
        original.expand::<3>().unwrap().polynomials
    );
}

/// Truncated containers and trailing data are rejected instead of returning partial rows.
#[test]
fn test_truncation_and_trailing_bytes() {
    let bytes = fixture();
    for end in 0..bytes.len() {
        assert!(
            R1cs::<Zp7>::parse(&bytes[..end], &ImportLimits::default()).is_err(),
            "prefix {end}"
        );
    }
    let mut extra = bytes;
    extra.push(0);
    assert!(matches!(
        R1cs::<Zp7>::parse(&extra, &ImportLimits::default()),
        Err(Error::TrailingBytes)
    ));
}

/// Missing, duplicate, unsupported and overflow-sized sections fail explicitly.
#[test]
fn test_section_validation() {
    let original = parts(&fixture());
    for missing in 1..=3 {
        let rest: Vec<_> = original
            .iter()
            .filter(|(kind, _)| *kind != missing)
            .cloned()
            .collect();
        assert!(
            matches!(R1cs::<Zp7>::parse(&container(&rest), &ImportLimits::default()), Err(Error::MissingSection(kind)) if kind==missing)
        );
    }
    let mut duplicate = original.clone();
    duplicate.push(original[0].clone());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&duplicate), &ImportLimits::default()),
        Err(Error::DuplicateSection(1))
    ));
    for unknown in [4, 5, 42] {
        let mut extended = original.clone();
        extended.push((unknown, vec![]));
        assert!(
            matches!(R1cs::<Zp7>::parse(&container(&extended), &ImportLimits::default()), Err(Error::UnsupportedSection(kind)) if kind==unknown)
        );
    }
    let mut huge = fixture();
    huge[16..24].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(R1cs::<Zp7>::parse(&huge, &ImportLimits::default()).is_err());
}

/// Version, modulus, prime-field type and inconsistent role counts are checked before rows.
#[test]
fn test_header_validation() {
    let mut bytes = fixture();
    bytes[0] = b'X';
    assert!(matches!(
        R1cs::<Zp7>::parse(&bytes, &ImportLimits::default()),
        Err(Error::InvalidMagic)
    ));
    bytes = fixture();
    bytes[4] = 2;
    assert!(matches!(
        R1cs::<Zp7>::parse(&bytes, &ImportLimits::default()),
        Err(Error::UnsupportedVersion(2))
    ));
    let mut fields = parts(&fixture());
    fields[0].1[4] = 11;
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&fields), &ImportLimits::default()),
        Err(Error::FieldMismatch)
    ));
    assert!(matches!(
        R1cs::<Gf256>::parse(&fixture(), &ImportLimits::default()),
        Err(Error::NonPrimeField)
    ));
    fields = parts(&fixture());
    fields[0].1[12..16].copy_from_slice(&0u32.to_le_bytes());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&fields), &ImportLimits::default()),
        Err(Error::InvalidHeader(_))
    ));
    fields = parts(&fixture());
    fields[0].1[16..20].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&fields), &ImportLimits::default()),
        Err(Error::InvalidHeader(_))
    ));
}

/// Linear combinations reject out-of-range, repeated or unordered wires and noncanonical coefficients.
#[test]
fn test_constraint_validation() {
    let mut sections = parts(&fixture());
    sections[1].1[4..8].copy_from_slice(&4u32.to_le_bytes());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()),
        Err(Error::InvalidWire { row: 0, wire: 4 })
    ));
    sections = parts(&fixture());
    sections[1].1[16..20].copy_from_slice(&0u32.to_le_bytes());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()),
        Err(Error::InvalidLinearCombination { row: 0 })
    ));
    for coefficient in [0, 7, u64::MAX] {
        sections = parts(&fixture());
        sections[1].1[8..16].copy_from_slice(&coefficient.to_le_bytes());
        assert!(matches!(
            R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()),
            Err(Error::NonCanonicalCoefficient { row: 0 })
        ));
    }
    sections = parts(&fixture());
    sections[1].1[..4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(
        R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()),
        Err(Error::InvalidLinearCombination { row: 0 })
    ));
}

/// Wire-label identity requires a unique in-range label per wire and label zero on wire zero.
#[test]
fn test_wire_label_validation() {
    for (offset, label) in [(0, 1u64), (8, 0), (24, 4)] {
        let mut sections = parts(&fixture());
        sections[2].1[offset..offset + 8].copy_from_slice(&label.to_le_bytes());
        assert!(matches!(
            R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()),
            Err(Error::InvalidWireMap)
        ));
    }
}

/// Parsing and expansion enforce structural limits and deadlines before accepting a result.
#[test]
fn test_import_and_expansion_limits() {
    let bytes = fixture();
    for limits in [
        ImportLimits {
            max_input_bytes: bytes.len() - 1,
            ..ImportLimits::default()
        },
        ImportLimits {
            max_wires: 3,
            ..ImportLimits::default()
        },
        ImportLimits {
            max_constraints: 2,
            ..ImportLimits::default()
        },
    ] {
        assert!(matches!(
            R1cs::<Zp7>::parse(&bytes, &limits),
            Err(Error::Limit { .. })
        ));
    }
    for limits in [
        ImportLimits {
            max_products: 1,
            ..ImportLimits::default()
        },
        ImportLimits {
            max_expanded_terms: 0,
            ..ImportLimits::default()
        },
    ] {
        let parsed = R1cs::<Zp7>::parse(&bytes, &limits).unwrap();
        assert!(matches!(parsed.expand::<3>(), Err(Error::Limit { .. })));
    }
    assert!(matches!(
        R1cs::<Zp7>::parse(
            &bytes,
            &ImportLimits {
                timeout: Duration::ZERO,
                ..ImportLimits::default()
            }
        ),
        Err(Error::Deadline)
    ));
}

/// Capacity refusal is explicit and spare const-generic coordinates never relabel active wires.
#[test]
fn test_const_generic_capacity() {
    let model = R1cs::<Zp7>::parse(&fixture(), &ImportLimits::default()).unwrap();
    assert!(matches!(
        model.expand::<2>(),
        Err(Error::Arity {
            needed: 3,
            capacity: 2
        })
    ));
    let padded = model.expand::<5>().unwrap();
    assert_eq!(padded.variable_to_wire, vec![1, 2, 3]);
    assert_eq!(
        padded.polynomials[0].eval(&[
            Zp7::new(2),
            Zp7::new(3),
            Zp7::new(4),
            Zp7::new(5),
            Zp7::new(6)
        ]),
        model
            .evaluate_assignment(&[Zp7::one(), Zp7::new(2), Zp7::new(3), Zp7::new(4)])
            .unwrap()[0]
    );
}

/// Over-budget capacities are refused on a small stack before allocating fixed exponent arrays.
#[test]
fn test_capacity_refusal_precedes_exponent_array_stack_allocation() {
    let model = R1cs::<Zp7>::parse(&fixture(), &ImportLimits::default()).unwrap();
    let result = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || model.expand::<100_000>())
        .unwrap()
        .join()
        .unwrap();
    assert!(matches!(
        result,
        Err(Error::Limit {
            resource: "polynomial capacity",
            limit: 99
        })
    ));
}

/// Assignment checks require every original wire and the implicit constant wire equal to one.
#[test]
fn test_assignment_guards() {
    let model = R1cs::<Zp7>::parse(&fixture(), &ImportLimits::default()).unwrap();
    assert!(matches!(
        model.evaluate_assignment(&[Zp7::one(); 3]),
        Err(Error::AssignmentLength {
            expected: 4,
            actual: 3
        })
    ));
    assert!(matches!(
        model.evaluate_assignment(&[Zp7::zero(); 4]),
        Err(Error::ConstantWire)
    ));
}

/// Empty systems and rows that cancel remain distinct original-row obligations.
#[test]
fn test_empty_and_cancelling_constraints() {
    let empty = R1cs::<Zp7>::parse(&encode(1, &[]), &ImportLimits::default()).unwrap();
    assert!(empty.expand::<0>().unwrap().polynomials.is_empty());
    assert!(empty.evaluate_assignment(&[Zp7::one()]).unwrap().is_empty());
    let cancellation = encode(2, &[[vec![(0, 1)], vec![(1, 1)], vec![(1, 1)]]]);
    let parsed = R1cs::<Zp7>::parse(&cancellation, &ImportLimits::default()).unwrap();
    let expanded = parsed.expand::<1>().unwrap();
    assert_eq!(expanded.row_ids, vec![0]);
    assert!(expanded.polynomials[0].is_zero());
    assert_eq!(expanded.stats.expanded_terms, 0);
}

/// Symbol records preserve optimized-out labels and aliases while rejecting ambiguous or invalid records.
#[test]
fn test_optional_symbols() {
    let parse = || {
        let mut sections = parts(&fixture());
        sections[0].1[28..36].copy_from_slice(&8u64.to_le_bytes());
        R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()).unwrap()
    };
    let one = parse()
        .with_symbols("2,2,0,main.a\n4,-1,1,main.removed\n5,2,0,main.alias\n")
        .unwrap();
    assert_eq!(one.symbols()[1].wire, None);
    assert_eq!(one.symbols()[2].wire, Some(2));
    let two = parse()
        .with_symbols("5,2,0,main.alias\n4,-1,1,main.removed\n2,2,0,main.a\n")
        .unwrap();
    assert_eq!(one.symbol_digest(), two.symbol_digest());
    assert_eq!(one.canonical_digest(), parse().canonical_digest());
    for text in [
        "1,4,0,bad",
        "8,1,0,bad",
        "1,-2,0,bad",
        "1,1,0,",
        "1,1,0,a\n1,2,0,b",
        "1,1,0,a\n2,2,0,a",
        "1,1,main.a",
    ] {
        assert!(
            matches!(parse().with_symbols(text), Err(Error::InvalidSymbol { .. })),
            "{text}"
        );
    }
}

/// Symbol-sidecar record counts have their own limit independent of text bytes and wire count.
#[test]
fn test_symbol_count_limit() {
    let model = R1cs::<Zp7>::parse(
        &fixture(),
        &ImportLimits {
            max_symbols: 1,
            ..ImportLimits::default()
        },
    )
    .unwrap();
    assert!(matches!(
        model.with_symbols("1,1,0,a\n2,2,0,b\n"),
        Err(Error::Limit {
            resource: "symbols",
            limit: 1
        })
    ));
}

/// Symbols for labels chosen by the binary map must name that same canonical witness wire.
#[test]
fn test_symbols_cannot_contradict_the_canonical_wire_map() {
    for text in [
        "1,2,0,wrong_wire",
        "1,-1,0,falsely_removed",
        "2,0,0,false_constant",
    ] {
        let model = R1cs::<Zp7>::parse(&fixture(), &ImportLimits::default()).unwrap();
        assert!(
            matches!(
                model.with_symbols(text),
                Err(Error::InvalidSymbol { line: 1 })
            ),
            "{text}"
        );
    }
}

/// Nonidentity labels never permute polynomial variables, and trailing witnesses remain internal.
#[test]
fn test_nonidentity_labels_and_internal_wires() {
    let mut sections = parts(&encode(5, &[[vec![(1, 1)], vec![(2, 1)], vec![(3, 1)]]]));
    sections[2].1 = [0u64, 4, 3, 2, 1]
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect();
    let model = R1cs::<Zp7>::parse(&container(&sections), &ImportLimits::default()).unwrap();
    assert_eq!(model.wire_labels(), &[0, 4, 3, 2, 1]);
    assert_eq!(model.wire_role(4), Some(WireRole::Internal));
    let expanded = model.expand::<4>().unwrap();
    assert_eq!(expanded.variable_to_wire, vec![1, 2, 3, 4]);
    assert!(expanded.polynomials[0]
        .eval(&[Zp7::new(2), Zp7::new(3), Zp7::new(6), Zp7::new(4)])
        .is_zero());
}

/// A constant-only impossible row remains a nonzero polynomial at arity zero.
#[test]
fn test_constant_only_impossible_constraint() {
    let bytes = encode(1, &[[vec![], vec![], vec![(0, 1)]]]);
    let model = R1cs::<Zp7>::parse(&bytes, &ImportLimits::default()).unwrap();
    let expanded = model.expand::<0>().unwrap();
    assert_eq!(expanded.polynomials.len(), 1);
    assert_eq!(expanded.polynomials[0].eval(&[]), -Zp7::one());
    assert_eq!(
        model.evaluate_assignment(&[Zp7::one()]).unwrap(),
        vec![-Zp7::one()]
    );
}
