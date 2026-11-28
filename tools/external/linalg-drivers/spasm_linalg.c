/* SpaSM comparand driver (#1209): sparse spasm_echelonize then spasm_rref, primes below 2^32.
 * MIT, part of Zeebra; links SpaSM (GPL) and runs only as a separate process.
 *
 * SpaSM chooses its own pivots, so its RREF is that of A*Q for a column permutation Q of its
 * choosing (upstream's warning in spasm_rref.c). The result is the canonical RREF exactly when
 * every row's pivot is its leftmost entry; the driver checks that and prints `canonical=1` or
 * `canonical=0`. With LINALG_DUMP=<path> set, it also writes R as SMS there, so the caller can
 * bring a permuted result to canonical form outside the timed region and compare digests.
 * `seconds` is echelonize plus rref; `echelon_seconds` is echelonize alone. Only multiplication
 * is unsupported: SpaSM has no general product. */
#include <omp.h>
#include <spasm.h>

#include "common.h"

typedef struct {
  const struct spasm_csr *R;
  const int *lead;
} order_t;

static const order_t *sort_context;

static int by_lead(const void *x, const void *y) {
  int a = *(const int *)x, b = *(const int *)y;
  return sort_context->lead[a] - sort_context->lead[b];
}

int main(int argc, char **argv) {
  args_t a = parse_args(argc, argv, "spasm", "SpaSM 1.3 @ 09c40943");
  if (!a.is_rref) die("SpaSM has no general matrix product");
  if (a.prime > 0xfffffffbULL) die("SpaSM's field is below 2^32");
  omp_set_num_threads(a.threads);
  triplets_t t = read_sms(a.path, a.prime);
  struct spasm_triplet *T = spasm_triplet_alloc(t.rows, t.cols, t.nnz, a.prime, true);
  for (size_t k = 0; k < t.nnz; k++)
    if (t.v[k]) spasm_add_entry(T, t.i[k], t.j[k], (i64)t.v[k]);
  struct spasm_csr *A = spasm_compress(T);
  spasm_triplet_free(T);
  const int m = A->m;
  const uint64_t p = a.prime;
  for (int rep = 0; rep < a.reps; rep++) {
    struct echelonize_opts opts;
    spasm_echelonize_init_opts(&opts);
    int *Rqinv = (int *)malloc(m * sizeof(int));
    double start = now_seconds();
    struct spasm_lu *fact = spasm_echelonize(A, &opts);
    double echelon_seconds = now_seconds() - start;
    struct spasm_csr *R = spasm_rref(fact, Rqinv);
    double seconds = now_seconds() - start;

    /* Each row of R stores its pivot first; columns are otherwise unsorted. */
    const int r = R->n;
    int *lead = (int *)malloc(r * sizeof(int)), *rows = (int *)malloc(r * sizeof(int));
    int canonical = 1;
    for (int i = 0; i < r; i++) {
      rows[i] = i;
      lead[i] = R->j[R->p[i]];
      for (i64 px = R->p[i]; px < R->p[i + 1]; px++)
        if (R->j[px] < lead[i]) canonical = 0;
    }
    order_t order = {R, lead};
    sort_context = &order;
    qsort(rows, r, sizeof(int), by_lead);

    fnv_t h;
    fnv_init(&h);
    fnv_word(&h, (uint64_t)t.rows);
    fnv_word(&h, (uint64_t)t.cols);
    fnv_word(&h, (uint64_t)r);
    uint64_t *dense = (uint64_t *)calloc(m, sizeof(uint64_t));
    const char *dump = getenv("LINALG_DUMP");
    FILE *out = (dump && rep == 0) ? fopen(dump, "w") : NULL;
    if (out) fprintf(out, "%ld %d M\n", (long)r, m);
    for (int k = 0; k < r; k++) {
      int i = rows[k];
      uint64_t count = 0;
      for (i64 px = R->p[i]; px < R->p[i + 1]; px++) {
        long long x = R->x[px];
        uint64_t v = (uint64_t)(x < 0 ? x + (long long)p : x);
        dense[R->j[px]] = v;
        count += v != 0;
      }
      fnv_word(&h, count);
      /* Walk the row's columns in increasing order through the scattered copy. */
      int lo = m, hi = -1;
      for (i64 px = R->p[i]; px < R->p[i + 1]; px++) {
        if (R->j[px] < lo) lo = R->j[px];
        if (R->j[px] > hi) hi = R->j[px];
      }
      for (int c = lo; c <= hi; c++)
        if (dense[c]) {
          fnv_word(&h, (uint64_t)c);
          fnv_word(&h, dense[c]);
          if (out) fprintf(out, "%d %d %" PRIu64 "\n", k + 1, c + 1, dense[c]);
          dense[c] = 0;
        }
    }
    if (out) {
      fprintf(out, "0 0 0\n");
      fclose(out);
    }
    printf("rref rows=%ld cols=%ld rank=%d digest=%016" PRIx64
           " seconds=%.6f echelon_seconds=%.6f canonical=%d\n",
           t.rows, t.cols, r, h.state, seconds, echelon_seconds, canonical);
    fflush(stdout);
    free(dense);
    free(lead);
    free(rows);
    free(Rqinv);
    spasm_csr_free(R);
    spasm_lu_free(fact);
  }
  spasm_csr_free(A);
  return 0;
}
