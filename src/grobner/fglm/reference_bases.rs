//! Lexicographic Gröbner bases computed by Singular, committed as literals.
//!
//! **Generated. Do not edit by hand.** Regenerate with
//!
//! ```text
//! Singular -q tools/reference_bases.sing > src/grobner/fglm/reference_bases.rs
//! ```
//!
//! Singular's `std` is Buchberger/slimgb lineage, so these are independent of Zeebra's F4
//! in algorithm and not only in implementation. Every basis below was also checked against
//! Singular's own `fglm` — a third algorithm — before being emitted.
//!
//! Singular build 44105. See tools/reference_bases.sing for the conventions this relies on,
//! each of which was verified rather than assumed.

/// One ideal and the lexicographic Gröbner basis Singular computed for it.
pub(super) struct ReferenceBasis {
    pub name: &'static str,
    pub prime: u64,
    pub variables: &'static [&'static str],
    pub system: &'static [&'static str],
    pub lex_basis: &'static [&'static str],
}

/// Two variables over GF(2^31 - 1).
pub(super) const TWO_VARIABLE: &[ReferenceBasis] = &[
    ReferenceBasis {
        name: "x^2, y^2",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^2", "y^2"],
        lex_basis: &["y^2", "x^2"],
    },
    ReferenceBasis {
        name: "x^2-y, y^3-1",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^2-y", "y^3-1"],
        lex_basis: &["y^3-1", "x^2-y"],
    },
    ReferenceBasis {
        name: "x+y, x*y-1",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x+y", "x*y-1"],
        lex_basis: &["y^2+1", "x+y"],
    },
    ReferenceBasis {
        name: "x^3-1, y-x^2",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^3-1", "y-x^2"],
        lex_basis: &["y^3-1", "x-y^2"],
    },
    ReferenceBasis {
        name: "(x-1)^2, y-x",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^2-2*x+1", "y-x"],
        lex_basis: &["y^2-2*y+1", "x-y"],
    },
    ReferenceBasis {
        name: "x^4-x, y^2-x",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^4-x", "y^2-x"],
        lex_basis: &["y^8-y^2", "x-y^2"],
    },
    ReferenceBasis {
        name: "x^2+y^2-1, x-y",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^2+y^2-1", "x-y"],
        lex_basis: &["y^2+1073741823", "x-y"],
    },
    ReferenceBasis {
        name: "x^5-1, y^3-x",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^5-1", "y^3-x"],
        lex_basis: &["y^15-1", "x-y^3"],
    },
    ReferenceBasis {
        name: "x^2+1, y^2+1",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^2+1", "y^2+1"],
        lex_basis: &["y^2+1", "x^2+1"],
    },
    ReferenceBasis {
        name: "2*x-3, y^2-x",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["2*x-3", "y^2-x"],
        lex_basis: &["y^2+1073741822", "x+1073741822"],
    },
    ReferenceBasis {
        name: "x^6-1, y^4-x^2",
        prime: 2147483647,
        variables: &["x", "y"],
        system: &["x^6-1", "y^4-x^2"],
        lex_basis: &["y^12-1", "x^2-y^4"],
    },
];

/// Three variables over GF(2^31 - 1).
pub(super) const THREE_VARIABLE: &[ReferenceBasis] = &[
    ReferenceBasis {
        name: "cyclic-3",
        prime: 2147483647,
        variables: &["x", "y", "z"],
        system: &["x+y+z", "x*y+y*z+x*z", "x*y*z-1"],
        lex_basis: &["z^3-1", "y^2+y*z+z^2", "x+y+z"],
    },
    ReferenceBasis {
        name: "katsura-3",
        prime: 2147483647,
        variables: &["x", "y", "z"],
        system: &["x^2+2*y^2+2*z^2-x", "2*x*y+2*y*z-y", "x+2*y+2*z-1"],
        lex_basis: &[
            "z^4+1022611260*z^3+1048176542*z^2+1048176542*z",
            "y+30*z^3+613566745*z^2-920350134*z",
            "x-60*z^3+920350157*z^2-306783377*z-1",
        ],
    },
    ReferenceBasis {
        name: "not in shape position",
        prime: 2147483647,
        variables: &["x", "y", "z"],
        system: &["x^2-1", "y^2-1", "z-1"],
        lex_basis: &["z-1", "y^2-1", "x^2-1"],
    },
    ReferenceBasis {
        name: "x^2-y, y^2-z, z^2-1",
        prime: 2147483647,
        variables: &["x", "y", "z"],
        system: &["x^2-y", "y^2-z", "z^2-1"],
        lex_basis: &["z^2-1", "y^2-z", "x^2-y"],
    },
    ReferenceBasis {
        name: "nonradical in three variables",
        prime: 2147483647,
        variables: &["x", "y", "z"],
        system: &["x^2", "y^2", "z^2"],
        lex_basis: &["z^2", "y^2", "x^2"],
    },
];

/// Four variables over GF(2^31 - 1).
pub(super) const FOUR_VARIABLE: &[ReferenceBasis] = &[
    ReferenceBasis {
        name: "katsura-4",
        prime: 2147483647,
        variables: &["x", "y", "z", "w"],
        system: &["x^2+2*y^2+2*z^2+2*w^2-x", "2*x*y+2*y*z+2*z*w-y", "2*x*z+y^2+2*y*w-z", "x+2*y+2*z+2*w-1"],
        lex_basis: &["w^8-585677359*w^7-260301048*w^6-609377608*w^5+681549555*w^4-597125784*w^3-248802410*w^2-699241055*w", "z-917763975*w^7-525552501*w^6+138848708*w^5+183214518*w^4-913950236*w^3+389127214*w^2+523517773*w", "y-289584400*w^7+236256647*w^6-953307919*w^5-138351634*w^4+194836050*w^3+716331969*w^2-211703688*w", "x+267213103*w^7+578591708*w^6-518565225*w^5-89725768*w^4-709255275*w^3-63434719*w^2-623628168*w-1"],
    },
    ReferenceBasis {
        name: "planted-4 at (3,5,7,11)",
        prime: 2147483647,
        variables: &["x", "y", "z", "w"],
        system: &["x^2+y^2-34", "x*y-15", "z^2+w^2-170", "z*w-77"],
        lex_basis: &["w^4-170*w^2+5929", "z-27889398*w^3+446230366*w", "y^4-34*y^2+225", "x+286331153*y^3+1002159033*y"],
    },
];

/// Two variables over GF(13).
pub(super) const OVER_GF_13: &[ReferenceBasis] = &[
    ReferenceBasis {
        name: "x^2-y, y^3-1",
        prime: 13,
        variables: &["x", "y"],
        system: &["x^2-y", "y^3-1"],
        lex_basis: &["y^3-1", "x^2-y"],
    },
    ReferenceBasis {
        name: "x^2, y^2",
        prime: 13,
        variables: &["x", "y"],
        system: &["x^2", "y^2"],
        lex_basis: &["y^2", "x^2"],
    },
    ReferenceBasis {
        name: "x+y, x*y-1",
        prime: 13,
        variables: &["x", "y"],
        system: &["x+y", "x*y-1"],
        lex_basis: &["y^2+1", "x+y"],
    },
    ReferenceBasis {
        name: "x^2+1, y-x",
        prime: 13,
        variables: &["x", "y"],
        system: &["x^2+1", "y-x"],
        lex_basis: &["y^2+1", "x-y"],
    },
    ReferenceBasis {
        name: "2*x-3, y^2-x",
        prime: 13,
        variables: &["x", "y"],
        system: &["2*x-3", "y^2-x"],
        lex_basis: &["y^2+5", "x+5"],
    },
];

/// Two variables over GF(65537).
pub(super) const OVER_GF_65537: &[ReferenceBasis] = &[
    ReferenceBasis {
        name: "x^2-y, y^3-1",
        prime: 65537,
        variables: &["x", "y"],
        system: &["x^2-y", "y^3-1"],
        lex_basis: &["y^3-1", "x^2-y"],
    },
    ReferenceBasis {
        name: "x^2, y^2",
        prime: 65537,
        variables: &["x", "y"],
        system: &["x^2", "y^2"],
        lex_basis: &["y^2", "x^2"],
    },
    ReferenceBasis {
        name: "x+y, x*y-1",
        prime: 65537,
        variables: &["x", "y"],
        system: &["x+y", "x*y-1"],
        lex_basis: &["y^2+1", "x+y"],
    },
    ReferenceBasis {
        name: "x^2+1, y-x",
        prime: 65537,
        variables: &["x", "y"],
        system: &["x^2+1", "y-x"],
        lex_basis: &["y^2+1", "x-y"],
    },
    ReferenceBasis {
        name: "2*x-3, y^2-x",
        prime: 65537,
        variables: &["x", "y"],
        system: &["2*x-3", "y^2-x"],
        lex_basis: &["y^2+32767", "x+32767"],
    },
];
