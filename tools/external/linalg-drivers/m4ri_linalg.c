/* M4RI comparand driver (#1209): dense GF(2) mzd_echelonize (full, M4RI's own choice of PLUQ or
 * M4RI) and mzd_mul (Strassen-Winograd at M4RI's default cutoff). MIT, part of Zeebra; links M4RI
 * (GPL) and runs only as a separate process. Built without OpenMP, so `threads` must be 1. */
#include <m4ri/m4ri.h>

#include "common.h"

#ifndef M4RI_VERSION_STRING
#define M4RI_VERSION_STRING "unknown"
#endif

static uint64_t digest_mzd(const mzd_t *m, long *rank_out) {
  long rows = m->nrows, cols = m->ncols, rank = 0;
  fnv_t h;
  fnv_init(&h);
  for (long r = 0; r < rows; r++)
    for (long c = 0; c < cols; c++)
      if (mzd_read_bit(m, r, c)) {
        rank++;
        break;
      }
  fnv_word(&h, (uint64_t)rows);
  fnv_word(&h, (uint64_t)cols);
  fnv_word(&h, (uint64_t)rank);
  for (long r = 0; r < rows; r++) {
    uint64_t count = 0;
    for (long c = 0; c < cols; c++) count += mzd_read_bit(m, r, c);
    if (!count) continue;
    fnv_word(&h, count);
    for (long c = 0; c < cols; c++)
      if (mzd_read_bit(m, r, c)) {
        fnv_word(&h, (uint64_t)c);
        fnv_word(&h, 1);
      }
  }
  *rank_out = rank;
  return h.state;
}

int main(int argc, char **argv) {
  args_t a = parse_args(argc, argv, "m4ri", "M4RI " M4RI_VERSION_STRING);
  if (a.prime != 2) die("M4RI is GF(2) only");
  if (a.threads != 1) die("this M4RI is built without OpenMP; run it at one thread");
  if (a.is_rref) {
    triplets_t t = read_sms(a.path, 2);
    for (int rep = 0; rep < a.reps; rep++) {
      mzd_t *m = mzd_init(t.rows, t.cols);
      for (size_t k = 0; k < t.nnz; k++)
        if (t.v[k]) mzd_write_bit(m, t.i[k], t.j[k], mzd_read_bit(m, t.i[k], t.j[k]) ^ 1);
      double start = now_seconds();
      rci_t rank = mzd_echelonize(m, 1);
      double seconds = now_seconds() - start;
      long counted;
      uint64_t digest = digest_mzd(m, &counted);
      if (counted != rank) die("rank and RREF disagree");
      print_rref(t.rows, t.cols, rank, digest, seconds);
      mzd_free(m);
    }
  } else {
    long n = a.n;
    uint64_t *buffer = (uint64_t *)malloc((size_t)n * n * sizeof(uint64_t));
    mzd_t *x = mzd_init(n, n), *y = mzd_init(n, n), *z = mzd_init(n, n);
    uint64_t state = a.seed;
    random_square(&state, 2, n, buffer);
    for (long k = 0; k < n * n; k++) mzd_write_bit(x, k / n, k % n, buffer[k]);
    random_square(&state, 2, n, buffer);
    for (long k = 0; k < n * n; k++) mzd_write_bit(y, k / n, k % n, buffer[k]);
    for (int rep = 0; rep < a.reps; rep++) {
      double start = now_seconds();
      mzd_mul(z, x, y, 0);
      double seconds = now_seconds() - start;
      fnv_t h;
      fnv_init(&h);
      for (long r = 0; r < n; r++)
        for (long c = 0; c < n; c++) fnv_word(&h, mzd_read_bit(z, r, c));
      print_mul(n, h.state, seconds);
    }
    mzd_free(x);
    mzd_free(y);
    mzd_free(z);
    free(buffer);
  }
  return 0;
}
