use std::{error::Error, fs::File, io::Read, path::Path, process::ExitCode, time::Instant};
use zeebra::{
    fields::{Bn254Fr, Zp7},
    r1cs::{ImportLimits, R1cs},
    util::{peak_resident_bytes, Json},
    KnownOrder,
};

struct Args {
    input: String,
    field: String,
    capacity: usize,
    symbols: Option<String>,
    assignment: Option<String>,
    limits: ImportLimits,
}

fn bounded_read(path: &Path, maximum: usize) -> Result<Vec<u8>, Box<dyn Error>> {
    let mut bytes = Vec::new();
    File::open(path)?
        .take((maximum as u64).saturating_add(1))
        .read_to_end(&mut bytes)?;
    if bytes.len() > maximum {
        return Err(zeebra::r1cs::Error::Limit {
            resource: "input bytes",
            limit: maximum,
        }
        .into());
    }
    Ok(bytes)
}

fn run<F: KnownOrder, const N: usize>(args: &Args) -> (Json, bool) {
    let start = Instant::now();
    let mut stage = "read";
    let mut report = vec![
        ("input", Json::string(&args.input)),
        ("field", Json::string(&args.field)),
        ("capacity", Json::size(N)),
        ("workers", Json::int(1)),
        ("seed", Json::int(0)),
        ("solve_ns", Json::Null),
        ("recovery_ns", Json::Null),
    ];
    let result = (|| -> Result<(), Box<dyn Error>> {
        let at = Instant::now();
        let read = bounded_read(Path::new(&args.input), args.limits.max_input_bytes);
        report.push(("read_ns", Json::nanos(at.elapsed())));
        let bytes = read?;
        report.push(("input_bytes", Json::size(bytes.len())));
        stage = "parse";
        let at = Instant::now();
        let parsed = R1cs::<F>::parse(&bytes, &args.limits);
        report.push(("parse_ns", Json::nanos(at.elapsed())));
        let mut model = parsed?;
        if let Some(path) = &args.symbols {
            stage = "symbols";
            let at = Instant::now();
            let symbols = bounded_read(Path::new(path), args.limits.max_input_bytes)?;
            model = model.with_symbols(std::str::from_utf8(&symbols)?)?;
            report.push(("symbols_ns", Json::nanos(at.elapsed())));
        }
        report.push(("source_digest", Json::string(model.source_digest())));
        report.push(("canonical_digest", Json::string(model.canonical_digest())));
        report.push((
            "symbol_digest",
            model
                .symbol_digest()
                .map(Json::string)
                .unwrap_or(Json::Null),
        ));
        report.push(("wires", Json::size(model.header().wire_count)));
        report.push(("public_outputs", Json::size(model.header().public_outputs)));
        report.push(("public_inputs", Json::size(model.header().public_inputs)));
        report.push((
            "declared_private_inputs",
            Json::size(model.header().private_inputs),
        ));
        report.push((
            "wire_roles",
            Json::Array(
                (0..model.header().wire_count)
                    .map(|wire| {
                        Json::string(format!(
                            "{:?}",
                            model
                                .wire_role(wire as u32)
                                .expect("original wire in range")
                        ))
                    })
                    .collect(),
            ),
        ));
        report.push(("constraints", Json::size(model.header().constraint_count)));
        report.push((
            "wire_labels",
            Json::Array(
                model
                    .wire_labels()
                    .iter()
                    .map(|label| Json::int(*label))
                    .collect(),
            ),
        ));
        stage = "expand";
        let at = Instant::now();
        let expansion = model.expand::<N>();
        report.push(("model_ns", Json::nanos(at.elapsed())));
        let expanded = expansion?;
        report.push(("source_terms", Json::size(expanded.stats.source_terms)));
        report.push(("products", Json::size(expanded.stats.products)));
        report.push(("expanded_terms", Json::size(expanded.stats.expanded_terms)));
        report.push(("max_row_terms", Json::size(expanded.stats.max_row_terms)));
        report.push((
            "row_ids",
            Json::Array(
                expanded
                    .row_ids
                    .iter()
                    .map(|row| Json::size(*row))
                    .collect(),
            ),
        ));
        report.push((
            "variable_to_wire",
            Json::Array(
                expanded
                    .variable_to_wire
                    .iter()
                    .map(|wire| Json::int(*wire))
                    .collect(),
            ),
        ));
        if let Some(assignment) = &args.assignment {
            stage = "assignment";
            let wires = assignment
                .split(',')
                .map(F::from_str)
                .collect::<Result<Vec<_>, _>>()?;
            let at = Instant::now();
            let evaluation = model.evaluate_assignment(&wires);
            report.push(("independent_check_ns", Json::nanos(at.elapsed())));
            let residuals = evaluation?;
            let at = Instant::now();
            let mut point = [F::zero(); N];
            point[..wires.len() - 1].copy_from_slice(&wires[1..]);
            let evaluated: Vec<_> = expanded
                .polynomials
                .iter()
                .map(|p| p.eval(&point))
                .collect();
            report.push(("polynomial_check_ns", Json::nanos(at.elapsed())));
            if residuals != evaluated {
                return Err("original rows and expanded polynomials disagree".into());
            }
            report.push(("evaluation_agrees", Json::Bool(true)));
            report.push((
                "assignment_satisfies",
                Json::Bool(residuals.iter().all(|value| value.is_zero())),
            ));
            report.push((
                "residuals",
                Json::Array(
                    residuals
                        .iter()
                        .map(|value| Json::string(value.to_string()))
                        .collect(),
                ),
            ));
        }
        Ok(())
    })();
    let complete = result.is_ok();
    match result {
        Ok(()) => report.push(("outcome", Json::string("complete"))),
        Err(error) => {
            report.push(("outcome", Json::string("refused")));
            report.push(("stage", Json::string(stage)));
            report.push(("error", Json::string(error.to_string())));
        }
    }
    report.push(("elapsed_ns", Json::nanos(start.elapsed())));
    report.push((
        "peak_rss_bytes",
        peak_resident_bytes().map(Json::int).unwrap_or(Json::Null),
    ));
    (Json::object(report), complete)
}

fn dispatch<F: KnownOrder>(args: &Args) -> Result<(Json, bool), Box<dyn Error>> {
    Ok(match args.capacity {
        0 => run::<F, 0>(args),
        1 => run::<F, 1>(args),
        2 => run::<F, 2>(args),
        3 => run::<F, 3>(args),
        4 => run::<F, 4>(args),
        6 => run::<F, 6>(args),
        8 => run::<F, 8>(args),
        16 => run::<F, 16>(args),
        32 => run::<F, 32>(args),
        64 => run::<F, 64>(args),
        99 => run::<F, 99>(args),
        _ => return Err("compiled capacities: 0,1,2,3,4,6,8,16,32,64,99".into()),
    })
}

fn main() -> ExitCode {
    let mut arguments = std::env::args().skip(1);
    let Some(input) = arguments.next() else {
        eprintln!("usage: r1cs_import INPUT --field 7|bn254 --capacity N [--symbols FILE] [--assignment 1,...] [--max-products N]");
        return ExitCode::FAILURE;
    };
    if input == "--help" {
        println!("usage: r1cs_import INPUT --field 7|bn254 --capacity N [--symbols FILE] [--assignment 1,...] [--max-products N]");
        return ExitCode::SUCCESS;
    }
    let result = (|| -> Result<(Json, bool), Box<dyn Error>> {
        let mut args = Args {
            input,
            field: "bn254".into(),
            capacity: 3,
            symbols: None,
            assignment: None,
            limits: ImportLimits::default(),
        };
        while let Some(flag) = arguments.next() {
            let value = arguments.next().ok_or("a flag is missing its value")?;
            match flag.as_str() {
                "--field" => args.field = value,
                "--capacity" => args.capacity = value.parse()?,
                "--symbols" => args.symbols = Some(value),
                "--assignment" => args.assignment = Some(value),
                "--max-products" => args.limits.max_products = value.parse()?,
                _ => return Err(format!("unknown flag {flag}").into()),
            }
        }
        match args.field.as_str() {
            "7" => dispatch::<Zp7>(&args),
            "bn254" => dispatch::<Bn254Fr>(&args),
            _ => Err("field must be 7 or bn254".into()),
        }
    })();
    match result {
        Ok((report, complete)) => {
            println!("{}", report.to_json());
            if complete {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(error) => {
            println!(
                "{}",
                Json::object([
                    ("outcome", Json::string("refused")),
                    ("stage", Json::string("arguments")),
                    ("error", Json::string(error.to_string()))
                ])
                .to_json()
            );
            ExitCode::FAILURE
        }
    }
}
