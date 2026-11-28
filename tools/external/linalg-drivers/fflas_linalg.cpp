// FFLAS-FFPACK comparand driver (#1209): ReducedRowEchelonForm (PLUQ, TileRecursive) and fgemm.
// MIT, part of Zeebra; links FFLAS-FFPACK and Givaro (LGPL) and runs only as a separate process.
//
// Primes below 2^26 run in Givaro::Modular<double>, FFLAS's own fast path through BLAS; larger
// primes below 2^31 in Modular<int64_t>. FFLAS has no word-size path above that, so a 64-bit
// prime is refused. One thread is the sequential routine; more is FFLAS's own OpenMP parallel
// routine (pReducedRowEchelonForm; fgemm, Recursive and TwoDAdaptive). BLAS stays single-threaded in both, which is what
// FFLAS's parallel routines expect.
#include <fflas-ffpack/fflas-ffpack-config.h>
#include <fflas-ffpack/fflas/fflas.h>
#include <fflas-ffpack/ffpack/ffpack.h>
#include <givaro/modular.h>

#include <vector>

#include "common.h"

template <class Field>
static void run(const args_t &a) {
  Field F(a.prime);
  typedef typename Field::Element Element;
  const size_t nt = (size_t)a.threads;
  if (a.is_rref) {
    triplets_t t = read_sms(a.path, a.prime);
    const size_t m = t.rows, n = t.cols;
    std::vector<uint64_t> input(m * n, 0);
    for (size_t k = 0; k < t.nnz; k++) {
      uint64_t &cell = input[(size_t)t.i[k] * n + t.j[k]];
      cell = (cell + t.v[k]) % a.prime;
    }
    std::vector<Element> A(m * n);
    std::vector<size_t> P(m), Qt(n);
    std::vector<uint64_t> out(m * n);
    for (int rep = 0; rep < a.reps; rep++) {
      for (size_t k = 0; k < m * n; k++) F.init(A[k], (int64_t)input[k]);
      double start = now_seconds();
      size_t rank;
      if (nt == 1) {
        rank = FFPACK::ReducedRowEchelonForm(F, m, n, A.data(), n, P.data(), Qt.data(), false,
                                             FFPACK::FfpackTileRecursive);
      } else {
        rank = FFPACK::pReducedRowEchelonForm(F, m, n, A.data(), n, P.data(), Qt.data(), false,
                                              nt, FFPACK::FfpackTileRecursive);
      }
      FFPACK::getReducedEchelonForm(F, FFLAS::FflasUpper, m, n, rank, Qt.data(), A.data(), n,
                                    FFPACK::FfpackTileRecursive);
      double seconds = now_seconds() - start;
      for (size_t k = 0; k < m * n; k++) {
        int64_t x;
        F.convert(x, A[k]);
        out[k] = k / n < rank ? (uint64_t)((x % (int64_t)a.prime + (int64_t)a.prime) %
                                           (int64_t)a.prime)
                              : 0;
      }
      long counted;
      uint64_t digest = rref_digest_dense(out.data(), m, n, n, &counted);
      if ((size_t)counted != rank) die("rank and RREF disagree");
      print_rref(m, n, (long)rank, digest, seconds);
    }
  } else {
    const size_t n = a.n;
    std::vector<uint64_t> buffer(n * n);
    std::vector<Element> X(n * n), Y(n * n), Z(n * n);
    uint64_t state = a.seed;
    random_square(&state, a.prime, n, buffer.data());
    for (size_t k = 0; k < n * n; k++) F.init(X[k], (int64_t)buffer[k]);
    random_square(&state, a.prime, n, buffer.data());
    for (size_t k = 0; k < n * n; k++) F.init(Y[k], (int64_t)buffer[k]);
    for (int rep = 0; rep < a.reps; rep++) {
      double start = now_seconds();
      if (nt == 1) {
        FFLAS::fgemm(F, FFLAS::FflasNoTrans, FFLAS::FflasNoTrans, n, n, n, F.one, X.data(), n,
                     Y.data(), n, F.zero, Z.data(), n);
      } else {
        PAR_BLOCK {
          FFLAS::ParSeqHelper::Parallel<FFLAS::CuttingStrategy::Recursive,
                                        FFLAS::StrategyParameter::TwoDAdaptive>
              par(nt);
          FFLAS::fgemm(F, FFLAS::FflasNoTrans, FFLAS::FflasNoTrans, n, n, n, F.one, X.data(), n,
                       Y.data(), n, F.zero, Z.data(), n, par);
        }
      }
      double seconds = now_seconds() - start;
      fnv_t h;
      fnv_init(&h);
      for (size_t k = 0; k < n * n; k++) {
        int64_t x;
        F.convert(x, Z[k]);
        fnv_word(&h, (uint64_t)((x % (int64_t)a.prime + (int64_t)a.prime) % (int64_t)a.prime));
      }
      print_mul(n, h.state, seconds);
    }
  }
}

extern "C" void openblas_set_num_threads(int);

int main(int argc, char **argv) {
  args_t a = parse_args(argc, argv, "fflas", "FFLAS-FFPACK " __FFLASFFPACK_PACKAGE_VERSION);
  openblas_set_num_threads(1);
  if (a.prime < (1ULL << 26)) {
    run<Givaro::Modular<double>>(a);
  } else if (a.prime < (1ULL << 31)) {
    run<Givaro::Modular<int64_t>>(a);
  } else {
    die("FFLAS-FFPACK has no word-size field for this prime");
  }
  return 0;
}
