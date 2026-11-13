use std::{
    fs::OpenOptions,
    io::{self, BufReader, BufWriter, Write},
    path::Path,
};

use zeebra::{
    fields::KnownOrder,
    grobner::f4::{
        macaulay::io::{read_matrix, write_matrix, write_sms, ReadLimits},
        matrix_corpus::{
            capture_matrix, fingerprint_of, visit_corpus_entry, visit_large_corpus_entry,
            MatrixEntryVisitor, MatrixSpec,
        },
        options::ReductionStrategy,
        structured::{eliminate_to, BlockPlan, RowForm},
    },
    linalg::Backend,
    MultivariatePolynomial,
};

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 || !matches!(args[0].as_str(), "dump" | "replay" | "sms") {
        eprintln!("usage: f4_matrix_files <dump|replay|sms> <corpus-label> <path>");
        std::process::exit(64);
    }
    let mut action = Action {
        mode: &args[0],
        path: Path::new(&args[2]),
        result: None,
    };
    if !visit_corpus_entry(&args[1], &mut action)
        && !visit_large_corpus_entry(&args[1], &mut action)
    {
        eprintln!("unknown corpus label: {}", args[1]);
        std::process::exit(64);
    }
    if let Err(error) = action.result.expect("a known entry is dispatched") {
        eprintln!("{}: {error}", args[0]);
        std::process::exit(1);
    }
}

struct Action<'a> {
    mode: &'a str,
    path: &'a Path,
    result: Option<Result<(), String>>,
}

impl MatrixEntryVisitor for Action<'_> {
    fn visit<const N: usize, F: KnownOrder>(
        &mut self,
        spec: &MatrixSpec,
        generators: fn() -> Vec<MultivariatePolynomial<N, F>>,
    ) {
        self.result = Some(self.run(spec, generators));
    }
}

impl Action<'_> {
    fn run<const N: usize, F: KnownOrder>(
        &self,
        spec: &MatrixSpec,
        generators: fn() -> Vec<MultivariatePolynomial<N, F>>,
    ) -> Result<(), String> {
        let options = spec.options.options();
        if self.mode == "dump" {
            // Refuse an existing output before paying for the capture.
            let file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(self.path)
                .map_err(|e| e.to_string())?;
            let result = (|| {
                let captured = capture_matrix(
                    spec.label,
                    &generators(),
                    spec.order,
                    &options,
                    spec.selector,
                )
                .map_err(|e| e.to_string())?;
                if captured.fingerprint != spec.fingerprint {
                    return Err("capture differs from the pinned corpus fingerprint".to_string());
                }
                let mut writer = BufWriter::new(file);
                write_matrix(&mut writer, &captured.matrix).map_err(|e| e.to_string())?;
                writer.flush().map_err(|e| e.to_string())
            })();
            if result.is_err() {
                let _ = std::fs::remove_file(self.path);
            }
            result?;
            println!("saved {} {}", spec.label, spec.fingerprint.digest);
            return Ok(());
        }

        let file = std::fs::File::open(self.path).map_err(|e| e.to_string())?;
        let limits = ReadLimits {
            max_rows: spec.fingerprint.rows,
            max_columns: spec.fingerprint.columns,
            max_nonzeros: spec.fingerprint.nonzeros,
            ..ReadLimits::default()
        };
        let mut matrix =
            read_matrix::<N, F>(&mut BufReader::new(file), limits).map_err(|e| e.to_string())?;
        if fingerprint_of(&matrix, spec.fingerprint.batch_index) != spec.fingerprint {
            return Err("archive differs from the pinned corpus fingerprint".into());
        }
        if self.mode == "sms" {
            // SMS goes to stdout so the archive remains the only path argument.
            let mut writer = BufWriter::new(io::stdout().lock());
            write_sms(&mut writer, matrix.matrix()).map_err(|e| e.to_string())?;
            return writer.flush().map_err(|e| e.to_string());
        }

        let plan = match options.reduction {
            ReductionStrategy::Unstructured => BlockPlan::Baseline,
            ReductionStrategy::Structured => BlockPlan::ReducersFirstBlock,
        };
        let form = if options.reduce_batch_rows {
            RowForm::Reduced
        } else {
            RowForm::Echelon
        };
        let outcome = eliminate_to(
            plan,
            form,
            Backend::Sparse,
            &mut matrix,
            options.live_entry_allowance::<F>(),
        )
        .map_err(|entries| {
            format!("elimination exceeded its live-entry allowance at {entries} entries")
        })?;
        println!(
            "replayed {} input={} output={} rank={}",
            spec.label,
            spec.fingerprint.digest,
            zeebra::grobner::f4::digest_of(&matrix),
            outcome.statistics.rank
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zeebra::{
        fields::Gf256Mq,
        grobner::{
            benchmark_systems::cyclic,
            f4::matrix_corpus::{corpus, large_corpus},
        },
    };

    // Dispatch visits every ordinary and large entry without invoking its lazy generator.
    #[test]
    fn dispatch_is_metadata_only_and_complete() {
        struct Count(usize);
        impl MatrixEntryVisitor for Count {
            fn visit<const N: usize, F: KnownOrder>(
                &mut self,
                spec: &MatrixSpec,
                _: fn() -> Vec<MultivariatePolynomial<N, F>>,
            ) {
                assert_eq!(N, spec.variables);
                self.0 += 1;
            }
        }
        let mut count = Count(0);
        for spec in corpus() {
            assert!(visit_corpus_entry(spec.label, &mut count));
        }
        for spec in large_corpus() {
            assert!(visit_large_corpus_entry(spec.label, &mut count));
        }
        assert!(!visit_corpus_entry("missing", &mut count));
        assert!(!visit_large_corpus_entry("missing", &mut count));
        assert_eq!(count.0, corpus().len() + large_corpus().len());
    }

    // A real capture replays from disk without generators and refuses overwrite and wrong identity.
    #[test]
    fn dump_and_replay_validate_the_pinned_matrix() {
        let directory =
            std::env::temp_dir().join(format!("zeebra-matrix-files-{}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        let path = directory.join("matrix.zbf4");
        let spec = corpus()
            .into_iter()
            .find(|spec| spec.label == "cyclic-5/lex/gf256/default")
            .unwrap();
        let mut action = Action {
            mode: "dump",
            path: &path,
            result: None,
        };
        action.run(&spec, cyclic::<5, Gf256Mq>).unwrap();
        assert!(action.run(&spec, cyclic::<5, Gf256Mq>).is_err());
        fn forbidden() -> Vec<MultivariatePolynomial<5, Gf256Mq>> {
            panic!("replay must not generate a system")
        }
        action.mode = "replay";
        action.run(&spec, forbidden).unwrap();
        let mut wrong = spec.clone();
        wrong.fingerprint.digest = "0000000000000000".into();
        assert!(action.run(&wrong, forbidden).is_err());
        action.mode = "sms";
        assert!(action.run(&spec, forbidden).is_err());
        std::fs::remove_dir_all(directory).unwrap();
    }
}
