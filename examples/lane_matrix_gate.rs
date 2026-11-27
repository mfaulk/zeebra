//! #945's matrix-level gate: one serial forward pass over a captured GF(31), GF(32003) or GF(2^31 - 1)
//! batch (the last in #1183's 31-bit lane).
//!
//! `lane_matrix_gate <archive.zmat> <vars> <gf31|gf32003|m31> <accumulator|lane> [dense-percent]`
//!
//! Loads the archive (untimed), puts the reducer block first, then times one forward pass: the
//! shipped accumulator kernel (`Backend::Adaptive`, what `F4Options::recommended()` runs) or the
//! `u32` lane kernel, with the lane's conversions in and out charged. Prints one JSON line with the
//! wall, the work counters and a SHA-256 of the eliminated matrix, so two arms are compared entry
//! for entry by digest. Run each arm as its own process, pinned, interleaved.
use std::{fs::File, io::BufReader, time::Instant};

use zeebra::{
    fields::{Zp2147483647, Zp31, Zp32003},
    grobner::f4::{
        macaulay::io::{read_matrix, ReadLimits},
        matrix_corpus::digest_of,
    },
    linalg::{lane::LaneKernel, reduce_rows_against_pivots_with, Backend},
    util::peak_resident_bytes,
    FiniteField,
};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 || args.len() > 5 {
        eprintln!(
            "usage: lane_matrix_gate <archive> <vars> <gf31|gf32003|m31> <accumulator|lane> [dense-percent]"
        );
        std::process::exit(64);
    }
    let dense_percent = args
        .get(4)
        .map_or(LaneKernel::default().dense_percent, |s| {
            s.parse().expect("a percentage")
        });
    macro_rules! dispatch {
        ($($n:literal),*) => {
            match (args[1].as_str(), args[2].as_str()) {
                $(
                    (stringify!($n), "gf31") => run::<$n, Zp31>(&args[0], &args[3], dense_percent),
                    (stringify!($n), "gf32003") => run::<$n, Zp32003>(&args[0], &args[3], dense_percent),
                    (stringify!($n), "m31") => run::<$n, Zp2147483647>(&args[0], &args[3], dense_percent),
                )*
                _ => {
                    eprintln!("unsupported vars/field {} {}", args[1], args[2]);
                    std::process::exit(64);
                }
            }
        };
    }
    dispatch!(10, 12, 15, 18, 20);
}

fn run<const N: usize, F: FiniteField>(path: &str, arm: &str, dense_percent: u32) {
    let limits = ReadLimits {
        max_rows: 1 << 24,
        max_columns: 1 << 24,
        max_nonzeros: 1 << 31,
        ..ReadLimits::default()
    };
    let file = File::open(path).expect("archive opens");
    let mut matrix =
        read_matrix::<N, F>(&mut BufReader::with_capacity(1 << 20, file), limits).expect("loads");
    let input_digest = digest_of(&matrix);
    let split = matrix.partition_reducers_first();
    let rss_before = peak_resident_bytes().unwrap_or(0);

    let clock = Instant::now();
    let statistics = match arm {
        "accumulator" => reduce_rows_against_pivots_with(
            Backend::Adaptive,
            matrix.matrix_mut(),
            split,
            usize::MAX,
        ),
        "lane" => {
            let lane = F::small_prime_lane()
                .or_else(F::prime31_lane)
                .expect("a lane prime");
            LaneKernel { dense_percent }.reduce_rows_against_pivots(
                &lane,
                matrix.matrix_mut(),
                split,
                usize::MAX,
            )
        }
        other => panic!("unknown arm {other}"),
    }
    .expect("no budget");
    let seconds = clock.elapsed().as_secs_f64();

    println!(
        "{{\"arm\":\"{arm}\",\"dense_percent\":{dense_percent},\"archive\":\"{path}\",\
         \"input_digest\":\"{input_digest}\",\"rows\":{},\"columns\":{},\"split\":{split},\
         \"forward_seconds\":{seconds:.3},\"rank\":{},\"zero_rows\":{},\"row_operations\":{},\
         \"final_nonzeros\":{},\"peak_nonzeros\":{},\"rss_after_load\":{rss_before},\
         \"peak_rss\":{},\"output_digest\":\"{}\"}}",
        matrix.num_rows(),
        matrix.num_columns(),
        statistics.rank,
        statistics.zero_rows,
        statistics.row_operations,
        statistics.final_nonzeros,
        statistics.peak_nonzeros,
        peak_resident_bytes().unwrap_or(0),
        digest_of(&matrix),
    );
}
