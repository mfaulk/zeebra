/* FLINT nmod_mat comparand driver (#1209): nmod_mat_rref and nmod_mat_mul, any word-size prime.
 * MIT, part of Zeebra; links FLINT (LGPL) and runs only as a separate process. */
#include <flint/flint.h>
#include <flint/nmod.h>
#include <flint/nmod_mat.h>

#include "common.h"

static void load(nmod_mat_t a, const triplets_t *t) {
  for (size_t k = 0; k < t->nnz; k++) {
    ulong sum = nmod_add(nmod_mat_entry(a, t->i[k], t->j[k]), t->v[k], a->mod);
    nmod_mat_entry(a, t->i[k], t->j[k]) = sum;
  }
}

int main(int argc, char **argv) {
  char library[64];
  snprintf(library, sizeof library, "FLINT %s", flint_version);
  args_t a = parse_args(argc, argv, "flint", library);
  flint_set_num_threads(a.threads);
  if (a.is_rref) {
    triplets_t t = read_sms(a.path, a.prime);
    uint64_t *dense = (uint64_t *)malloc((size_t)t.rows * t.cols * sizeof(uint64_t));
    for (int rep = 0; rep < a.reps; rep++) {
      nmod_mat_t m;
      nmod_mat_init(m, t.rows, t.cols, a.prime);
      load(m, &t);
      double start = now_seconds();
      slong rank = nmod_mat_rref(m);
      double seconds = now_seconds() - start;
      for (long r = 0; r < t.rows; r++)
        for (long c = 0; c < t.cols; c++) dense[r * t.cols + c] = nmod_mat_entry(m, r, c);
      long counted;
      uint64_t digest = rref_digest_dense(dense, t.rows, t.cols, t.cols, &counted);
      if (counted != rank) die("rank and RREF disagree");
      print_rref(t.rows, t.cols, rank, digest, seconds);
      nmod_mat_clear(m);
    }
    free(dense);
  } else {
    long n = a.n;
    uint64_t *buffer = (uint64_t *)malloc((size_t)n * n * sizeof(uint64_t));
    nmod_mat_t x, y, z;
    nmod_mat_init(x, n, n, a.prime);
    nmod_mat_init(y, n, n, a.prime);
    nmod_mat_init(z, n, n, a.prime);
    uint64_t state = a.seed;
    random_square(&state, a.prime, n, buffer);
    for (long k = 0; k < n * n; k++) nmod_mat_entry(x, k / n, k % n) = buffer[k];
    random_square(&state, a.prime, n, buffer);
    for (long k = 0; k < n * n; k++) nmod_mat_entry(y, k / n, k % n) = buffer[k];
    for (int rep = 0; rep < a.reps; rep++) {
      double start = now_seconds();
      nmod_mat_mul(z, x, y);
      double seconds = now_seconds() - start;
      fnv_t h;
      fnv_init(&h);
      for (long r = 0; r < n; r++)
        for (long c = 0; c < n; c++) fnv_word(&h, nmod_mat_entry(z, r, c));
      print_mul(n, h.state, seconds);
    }
    nmod_mat_clear(x);
    nmod_mat_clear(y);
    nmod_mat_clear(z);
    free(buffer);
  }
  flint_cleanup_master();
  return 0;
}
