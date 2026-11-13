use std::io::{self, Read, Write};

use super::MacaulayMatrix;
use crate::{
    fields::KnownOrder,
    grobner::f4::{
        matrix_corpus::digest_of,
        symbolic::{PreprocessedRow, RowKind},
    },
    linalg::sparse::{SparseMatrix, SparseRow},
    FiniteField, Monomial,
};

const MAGIC: &[u8; 8] = b"ZBF4MAT\x01";

/// Allocation limits for loading an archive; these do not bound subsequent elimination fill-in.
#[derive(Clone, Copy, Debug)]
pub struct ReadLimits {
    pub max_rows: usize,
    pub max_columns: usize,
    pub max_nonzeros: usize,
    /// Maximum UTF-8 byte length of a field name or one coefficient.
    pub max_string_bytes: usize,
}

impl Default for ReadLimits {
    fn default() -> Self {
        Self {
            max_rows: 100_000,
            max_columns: 100_000,
            max_nonzeros: 32_000_000,
            max_string_bytes: 4096,
        }
    }
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn write_count(writer: &mut impl Write, value: usize) -> io::Result<()> {
    let value = u64::try_from(value).map_err(|_| invalid("count exceeds u64"))?;
    writer.write_all(&value.to_le_bytes())
}

fn read_count(reader: &mut impl Read, limit: usize) -> io::Result<usize> {
    let mut bytes = [0; 8];
    reader.read_exact(&mut bytes)?;
    let count =
        usize::try_from(u64::from_le_bytes(bytes)).map_err(|_| invalid("count exceeds usize"))?;
    if count > limit {
        return Err(invalid("archive exceeds read limit"));
    }
    Ok(count)
}

fn write_string(writer: &mut impl Write, value: &str) -> io::Result<()> {
    write_count(writer, value.len())?;
    writer.write_all(value.as_bytes())
}

fn read_string(reader: &mut impl Read, limit: usize) -> io::Result<String> {
    let size = read_count(reader, limit)?;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(size)
        .map_err(|_| invalid("cannot allocate string"))?;
    bytes.resize(size, 0);
    reader.read_exact(&mut bytes)?;
    String::from_utf8(bytes).map_err(|_| invalid("invalid UTF-8"))
}

fn write_monomial<const N: usize>(
    writer: &mut impl Write,
    monomial: &Monomial<N>,
) -> io::Result<()> {
    for exponent in monomial.exponents() {
        writer.write_all(&exponent.to_le_bytes())?;
    }
    Ok(())
}

fn read_monomial<const N: usize>(reader: &mut impl Read) -> io::Result<Monomial<N>> {
    let mut exponents = [0; N];
    for exponent in &mut exponents {
        let mut bytes = [0; 4];
        reader.read_exact(&mut bytes)?;
        *exponent = u32::from_le_bytes(bytes);
    }
    Ok(Monomial::new(&exponents))
}

/// Stream a version-1 native archive, preserving column order, empty rows and row provenance.
///
/// Coefficients use the `FiniteField` Display/from_str round trip, including extension fields.
/// The format is documented in `docs/guide/f4-matrix-files.md`; buffer file writers externally.
///
/// # Errors
/// Propagates output errors. The caller must flush its writer and discard partial output on failure.
pub fn write_matrix<const N: usize, F: FiniteField>(
    writer: &mut impl Write,
    matrix: &MacaulayMatrix<N, F>,
) -> io::Result<()> {
    writer.write_all(MAGIC)?;
    write_count(writer, N)?;
    write_string(writer, std::any::type_name::<F>())?;
    write_count(writer, matrix.num_rows())?;
    write_count(writer, matrix.num_columns())?;
    write_count(writer, matrix.nonzeros())?;
    for monomial in matrix.columns() {
        write_monomial(writer, monomial)?;
    }
    for (origin, row) in matrix.row_origins().iter().zip(matrix.matrix().rows()) {
        let (tag, pair) = match origin.kind {
            RowKind::Reducer => (0, 0),
            RowKind::PairComponent { pair } => (1, pair),
        };
        writer.write_all(&[tag])?;
        write_count(writer, origin.basis_index)?;
        write_count(writer, pair)?;
        write_monomial(writer, &origin.multiplier)?;
        write_count(writer, row.nonzeros())?;
        for (column, coefficient) in row.entries() {
            write_count(writer, *column)?;
            write_string(writer, &coefficient.to_string())?;
        }
    }
    writer.write_all(digest_of(matrix).as_bytes())
}

/// Load one complete native archive without executing F4.
///
/// Field identity and arity must match exactly. Sparse rows are validated, and the stored corpus
/// digest detects accidental corruption; it is not an authenticity guarantee. No generator basis,
/// F4 options or batch index is stored. Check against the intended corpus fingerprint before using
/// structured elimination, whose reducer-block invariants are stronger than sparse canonicality.
///
/// # Errors
/// Refuses incompatible versions/types, exceeded limits, noncanonical rows, duplicate columns,
/// inconsistent counts, digest mismatches and trailing data. Propagates input errors and EOF.
pub fn read_matrix<const N: usize, F: FiniteField>(
    reader: &mut impl Read,
    limits: ReadLimits,
) -> io::Result<MacaulayMatrix<N, F>> {
    let mut magic = [0; 8];
    reader.read_exact(&mut magic)?;
    if &magic != MAGIC {
        return Err(invalid("unknown matrix archive version"));
    }
    if read_count(reader, usize::MAX)? != N {
        return Err(invalid("matrix arity mismatch"));
    }
    if read_string(reader, limits.max_string_bytes)? != std::any::type_name::<F>() {
        return Err(invalid("matrix field identity mismatch"));
    }
    let num_rows = read_count(reader, limits.max_rows)?;
    let num_columns = read_count(reader, limits.max_columns)?;
    let nonzeros = read_count(reader, limits.max_nonzeros)?;
    if nonzeros > num_rows.saturating_mul(num_columns) {
        return Err(invalid("impossible nonzero count"));
    }
    let mut columns = Vec::new();
    columns
        .try_reserve_exact(num_columns)
        .map_err(|_| invalid("cannot allocate columns"))?;
    let mut seen = crate::poly::MonomialSet::default();
    for _ in 0..num_columns {
        let monomial = read_monomial(reader)?;
        if !seen.insert(monomial) {
            return Err(invalid("duplicate matrix column"));
        }
        columns.push(monomial);
    }
    drop(seen);
    let mut rows = Vec::new();
    let mut origins = Vec::new();
    rows.try_reserve_exact(num_rows)
        .map_err(|_| invalid("cannot allocate rows"))?;
    origins
        .try_reserve_exact(num_rows)
        .map_err(|_| invalid("cannot allocate origins"))?;
    let mut remaining = nonzeros;
    for _ in 0..num_rows {
        let mut tag = [0];
        reader.read_exact(&mut tag)?;
        let basis_index = read_count(reader, usize::MAX)?;
        let pair = read_count(reader, usize::MAX)?;
        let kind = match (tag[0], pair) {
            (0, 0) => RowKind::Reducer,
            (1, pair) => RowKind::PairComponent { pair },
            _ => return Err(invalid("invalid row origin")),
        };
        let multiplier = read_monomial(reader)?;
        let count = read_count(reader, remaining.min(num_columns))?;
        remaining -= count;
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(count)
            .map_err(|_| invalid("cannot allocate entries"))?;
        for _ in 0..count {
            let column = read_count(reader, num_columns.saturating_sub(1))?;
            let text = read_string(reader, limits.max_string_bytes)?;
            let coefficient =
                F::from_str(&text).map_err(|_| invalid("invalid field coefficient"))?;
            if coefficient.to_string() != text {
                return Err(invalid("noncanonical field coefficient"));
            }
            entries.push((column, coefficient));
        }
        rows.push(SparseRow::from_sorted(entries).map_err(|_| invalid("noncanonical sparse row"))?);
        origins.push(PreprocessedRow {
            multiplier,
            basis_index,
            kind,
        });
    }
    if remaining != 0 {
        return Err(invalid("incorrect nonzero count"));
    }
    let matrix = MacaulayMatrix {
        columns,
        matrix: SparseMatrix::new(num_columns, rows),
        rows: origins,
    };
    let mut digest = [0; 16];
    reader.read_exact(&mut digest)?;
    if digest != digest_of(&matrix).as_bytes() {
        return Err(invalid("matrix digest mismatch"));
    }
    let mut trailing = [0];
    if reader.read(&mut trailing)? != 0 {
        return Err(invalid("trailing matrix data"));
    }
    Ok(matrix)
}

/// Write SMS integer/modular triples, with one-based indices and the `0 0 0` terminator.
///
/// SMS carries no modulus or monomial/provenance labels; configure the receiving tool's field
/// separately. Extension fields are refused because their representation integers are not residues.
///
/// # Errors
/// Refuses extension fields before writing; otherwise propagates output errors.
pub fn write_sms<F: KnownOrder>(
    writer: &mut impl Write,
    matrix: &SparseMatrix<F>,
) -> io::Result<()> {
    if F::order_limbs() != F::characteristic_limbs() {
        return Err(invalid("SMS export requires a prime field"));
    }
    writeln!(writer, "{} {} M", matrix.num_rows(), matrix.num_columns())?;
    for (index, row) in matrix.rows().iter().enumerate() {
        for (column, coefficient) in row.entries() {
            writeln!(writer, "{} {} {}", index + 1, column + 1, coefficient)?;
        }
    }
    writeln!(writer, "0 0 0")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{Bn254Fr, Gf13Pow4, Gf256Mq, Zp13},
        grobner::f4::symbolic::{PreprocessedRow, RowKind},
        linalg::sparse::{SparseMatrix, SparseRow},
        Monomial,
    };

    fn fixture<F: FiniteField>() -> MacaulayMatrix<2, F> {
        MacaulayMatrix {
            columns: vec![
                Monomial::new(&[2, 0]),
                Monomial::new(&[0, 1]),
                Monomial::one(),
            ],
            matrix: SparseMatrix::new(
                3,
                vec![
                    SparseRow::new(&[(0, F::one()), (2, -F::one())]),
                    SparseRow::zero(),
                    SparseRow::new(&[(1, F::one())]),
                ],
            ),
            rows: vec![
                PreprocessedRow {
                    multiplier: Monomial::new(&[1, 0]),
                    basis_index: 7,
                    kind: RowKind::Reducer,
                },
                PreprocessedRow {
                    multiplier: Monomial::one(),
                    basis_index: 8,
                    kind: RowKind::PairComponent { pair: 2 },
                },
                PreprocessedRow {
                    multiplier: Monomial::one(),
                    basis_index: 9,
                    kind: RowKind::PairComponent { pair: 2 },
                },
            ],
        }
    }

    fn encoded<F: FiniteField>() -> Vec<u8> {
        let mut bytes = Vec::new();
        write_matrix(&mut bytes, &fixture::<F>()).unwrap();
        bytes
    }

    // A native round trip preserves every column, coefficient, empty row and row origin.
    #[test]
    fn round_trip_preserves_matrix_and_elimination() {
        fn check<F: FiniteField>() {
            let mut original = fixture::<F>();
            let mut restored =
                read_matrix::<2, F>(&mut encoded::<F>().as_slice(), ReadLimits::default()).unwrap();
            assert_eq!(original, restored);
            assert_eq!(
                crate::linalg::sparse::reduced_row_echelon(original.matrix_mut()),
                crate::linalg::sparse::reduced_row_echelon(restored.matrix_mut())
            );
            assert_eq!(original.matrix(), restored.matrix());
        }
        check::<Zp13>();
        check::<Gf256Mq>();
        check::<Bn254Fr>();
        check::<Gf13Pow4>();
    }

    // Wrong field, arity, version, truncation, trailing data and corruption cannot yield a matrix.
    #[test]
    fn refuses_incompatible_and_damaged_archives() {
        let bytes = encoded::<Zp13>();
        assert!(read_matrix::<2, Gf256Mq>(&mut bytes.as_slice(), ReadLimits::default()).is_err());
        assert!(read_matrix::<3, Zp13>(&mut bytes.as_slice(), ReadLimits::default()).is_err());
        for length in 0..bytes.len() {
            assert!(
                read_matrix::<2, Zp13>(&mut &bytes[..length], ReadLimits::default()).is_err(),
                "accepted prefix {length}"
            );
        }
        let mut altered = bytes.clone();
        altered[7] = 99;
        assert!(read_matrix::<2, Zp13>(&mut altered.as_slice(), ReadLimits::default()).is_err());
        let mut altered = bytes.clone();
        altered.push(0);
        assert!(read_matrix::<2, Zp13>(&mut altered.as_slice(), ReadLimits::default()).is_err());
        let mut altered = bytes;
        *altered.last_mut().unwrap() ^= 1;
        assert!(read_matrix::<2, Zp13>(&mut altered.as_slice(), ReadLimits::default()).is_err());
    }

    // Declared shape and entry counts are refused before reading or allocating their bodies.
    #[test]
    fn enforces_read_limits() {
        let bytes = encoded::<Zp13>();
        for limits in [
            ReadLimits {
                max_rows: 2,
                ..ReadLimits::default()
            },
            ReadLimits {
                max_columns: 2,
                ..ReadLimits::default()
            },
            ReadLimits {
                max_nonzeros: 2,
                ..ReadLimits::default()
            },
            ReadLimits {
                max_string_bytes: 1,
                ..ReadLimits::default()
            },
        ] {
            assert_eq!(
                read_matrix::<2, Zp13>(&mut bytes.as_slice(), limits)
                    .unwrap_err()
                    .kind(),
                std::io::ErrorKind::InvalidData
            );
        }
    }

    // Empty and zero-width matrices preserve their dimensions and zero rows.
    #[test]
    fn empty_matrices_round_trip() {
        for rows in [0, 3] {
            let matrix = MacaulayMatrix::<0, Zp13> {
                columns: Vec::new(),
                matrix: SparseMatrix::zero(rows, 0),
                rows: vec![
                    PreprocessedRow {
                        multiplier: Monomial::one(),
                        basis_index: 0,
                        kind: RowKind::PairComponent { pair: 0 }
                    };
                    rows
                ],
            };
            let mut bytes = Vec::new();
            write_matrix(&mut bytes, &matrix).unwrap();
            assert_eq!(
                read_matrix::<0, Zp13>(&mut bytes.as_slice(), ReadLimits::default()).unwrap(),
                matrix
            );
        }
    }

    // Extension representations and wide residues survive without integer embedding or narrowing.
    #[test]
    fn coefficients_preserve_the_whole_field() {
        fn check<F: FiniteField>(text: &str) {
            let mut matrix = fixture::<F>();
            *matrix.matrix_mut() = SparseMatrix::new(
                3,
                vec![
                    SparseRow::new(&[(2, F::from_str(text).unwrap())]),
                    SparseRow::zero(),
                    SparseRow::zero(),
                ],
            );
            let mut bytes = Vec::new();
            write_matrix(&mut bytes, &matrix).unwrap();
            assert_eq!(
                read_matrix::<2, F>(&mut bytes.as_slice(), ReadLimits::default()).unwrap(),
                matrix
            );
        }
        check::<Gf256Mq>("173");
        check::<Gf13Pow4>("[2, 3, 4, 5]");
        check::<Bn254Fr>("123456789012345678901234567890123456789");
    }

    // Invalid sparse structure is rejected before a constructor can panic or repair the input.
    #[test]
    fn rejects_invalid_structure() {
        let bytes = encoded::<Zp13>();
        let dimensions = 24 + std::any::type_name::<Zp13>().len();
        let columns = dimensions + 24;
        let first_row = columns + 3 * 2 * 4;
        let first_entry = first_row + 1 + 8 + 8 + 2 * 4 + 8;
        let second_entry = first_entry + 8 + 8 + 1;
        let reject = |bytes: Vec<u8>| {
            assert_eq!(
                read_matrix::<2, Zp13>(&mut bytes.as_slice(), ReadLimits::default())
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::InvalidData
            );
        };
        let mut altered = bytes.clone();
        altered[columns + 8..columns + 16].copy_from_slice(&bytes[columns..columns + 8]);
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_row] = 2;
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_row + 9] = 1;
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_entry..first_entry + 8].copy_from_slice(&3u64.to_le_bytes());
        reject(altered);
        let mut altered = bytes.clone();
        altered[second_entry..second_entry + 8].copy_from_slice(&0u64.to_le_bytes());
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_entry + 16] = b'0';
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_entry + 16] = b'!';
        reject(altered);
        let mut altered = bytes.clone();
        altered[first_entry + 16] = 255;
        reject(altered);
        let mut altered = bytes;
        altered[first_row + 25..first_row + 33].copy_from_slice(&4u64.to_le_bytes());
        reject(altered);
    }

    // The writer returns underlying I/O errors instead of treating a partial file as successful.
    #[test]
    fn propagates_output_errors() {
        struct Fails;
        impl io::Write for Fails {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::Error::other("disk full"))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        assert!(write_matrix(&mut Fails, &fixture::<Zp13>()).is_err());
        assert!(write_sms(&mut Fails, fixture::<Zp13>().matrix()).is_err());
    }

    // SMS uses sorted one-based integer entries and retains dimensions including empty rows.
    #[test]
    fn sms_matches_the_external_format_and_refuses_extensions() {
        let mut bytes = Vec::new();
        write_sms(&mut bytes, fixture::<Zp13>().matrix()).unwrap();
        assert_eq!(
            String::from_utf8(bytes).unwrap(),
            "3 3 M\n1 1 1\n1 3 12\n3 2 1\n0 0 0\n"
        );
        let mut bytes = Vec::new();
        assert!(write_sms(&mut bytes, fixture::<Gf256Mq>().matrix()).is_err());
        assert!(bytes.is_empty());
    }
}
