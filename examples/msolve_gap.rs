//! Per-batch F4 work on the digest-pinned `mq-random-10`, for setting beside msolve's verbose log (#737).
//!
//! `--write-input <path>` writes msolve's input file for the same digest and exits.
use std::{env, fs};
use zeebra::{
    fields::{Zp2147483647, Zp32003},
    grobner::{
        external::{corpus, msolve},
        f4::{
            macaulay::MacaulayMatrix,
            observer::BatchObserver,
            symbolic::{MonicBasis, RowKind},
        },
        f4_observed,
        pairs::CriticalPair,
        F4Options,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

#[derive(Default)]
struct Batch {
    degree: u64,
    pairs: usize,
    basis_before: usize,
    rows: usize,
    reducer_rows: usize,
    columns: usize,
    nonzeros: usize,
}

#[derive(Default)]
struct Shape {
    batches: Vec<Batch>,
}

impl<const N: usize, F: FiniteField> BatchObserver<N, F> for Shape {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]) {
        self.batches.push(Batch {
            degree: pairs.iter().map(|p| p.degree).max().unwrap_or(0),
            pairs: pairs.len(),
            basis_before: basis.len(),
            ..Batch::default()
        });
    }

    fn matrix(&mut self, matrix: &MacaulayMatrix<N, F>) {
        let batch = self.batches.last_mut().expect("matrix follows its batch");
        batch.rows = matrix.num_rows();
        batch.columns = matrix.num_columns();
        batch.nonzeros = matrix.nonzeros();
        batch.reducer_rows = matrix
            .row_origins()
            .iter()
            .filter(|row| matches!(row.kind, RowKind::Reducer))
            .count();
    }
}

fn run<F: FiniteField>(modulus: u64) {
    let order = MonomialOrder::GradedReverseLexicographic;
    let input = corpus::instance("mq-random-10", modulus, order).expect("published MQ10");
    let names: [&str; 10] = std::array::from_fn(|i| input.variables[i].as_str());
    let system: Vec<MultivariatePolynomial<10, F>> = input
        .system
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    let mut shape = Shape::default();
    let options = F4Options {
        measure_stages: true,
        ..F4Options::default()
    };
    let (basis, statistics) =
        f4_observed(&system, order, &options, &mut shape).expect("within limits");
    println!("# mq-random-10 GF({modulus}) digest {}", input.digest());
    println!("batch\tdeg\tpairs\tbasis_before\trows\treducer_rows\tcols\tnnz");
    for (i, b) in shape.batches.iter().enumerate() {
        println!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            i + 1,
            b.degree,
            b.pairs,
            b.basis_before,
            b.rows,
            b.reducer_rows,
            b.columns,
            b.nonzeros
        );
    }
    let sum = |f: fn(&Batch) -> usize| shape.batches.iter().map(f).sum::<usize>();
    println!(
        "# totals: batches {} rows {} reducer_rows {} nnz_as_built {} row_operations {} \
         reduced_basis {} final_nonzeros {}",
        shape.batches.len(),
        sum(|b| b.rows),
        sum(|b| b.reducer_rows),
        sum(|b| b.nonzeros),
        statistics.row_operations,
        basis.len(),
        statistics.total_final_nonzeros,
    );
    let ms = |d: std::time::Duration| d.as_secs_f64() * 1e3;
    let t = statistics.stages;
    println!(
        "# stages_ms: total {:.1} symbolic {:.1} construction {:.1} elimination {:.1} \
         extraction {:.1} interreduction {:.1}",
        ms(statistics.total),
        ms(t.symbolic),
        ms(t.construction),
        ms(t.elimination),
        ms(t.extraction),
        ms(t.interreduction),
    );
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let value = |name: &str| {
        args.iter()
            .position(|a| a == name)
            .and_then(|i| args.get(i + 1).cloned())
    };
    let modulus: u64 = value("--characteristic")
        .map(|s| s.parse().expect("integer characteristic"))
        .unwrap_or(32003);
    if let Some(path) = value("--write-input") {
        let input = corpus::instance(
            "mq-random-10",
            modulus,
            MonomialOrder::GradedReverseLexicographic,
        )
        .expect("published MQ10");
        fs::write(&path, msolve::input_file(&input)).expect("writable path");
        return;
    }
    match modulus {
        32003 => run::<Zp32003>(modulus),
        2147483647 => run::<Zp2147483647>(modulus),
        other => panic!("mq-random-10 is published at 32003 and 2147483647, not {other}"),
    }
}
