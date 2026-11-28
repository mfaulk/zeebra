/* Shared by every linear-algebra comparand driver (#1209). MIT, part of Zeebra.
 *
 * The protocol, which examples/linalg_comparands.rs prints identically for Zeebra's arms:
 *
 *   linalg-<name> --version
 *   linalg-<name> rref <matrix.sms> <prime> <threads> <reps>
 *   linalg-<name> mul <n> <prime> <seed> <threads> <reps>
 *
 * `rref` prints one line per repetition, `rref rows=R cols=C rank=K digest=D seconds=S`, where D is
 * the canonical digest of the reduced row echelon form (rref_digest_*); `mul` prints
 * `mul n=N digest=D seconds=S`, D being the digest of the product. Only the library's own
 * elimination or product is timed: reading, conversion and digesting are not.
 *
 * Digests are FNV-1a over 64-bit little-endian words, so a driver and Zeebra agree exactly when
 * their results are entry-for-entry equal. The RREF words are rows, columns and rank, then for
 * each nonzero row in increasing pivot column its entry count and its (column, value) pairs in
 * increasing column, values in [0, p). The product words are the n*n entries in row-major order.
 * The operands of `mul` come from splitmix64(seed): A row-major, then B, each entry next() % p. */
#ifndef ZEEBRA_LINALG_COMMON_H
#define ZEEBRA_LINALG_COMMON_H

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define LINALG_CONTRACT 1

#ifndef DRIVER_CFLAGS
#define DRIVER_CFLAGS "unknown"
#endif

typedef struct {
  uint64_t state;
} fnv_t;

static inline void fnv_init(fnv_t *h) { h->state = 0xcbf29ce484222325ULL; }

static inline void fnv_word(fnv_t *h, uint64_t w) {
  for (int i = 0; i < 8; i++) {
    h->state ^= (w >> (8 * i)) & 0xff;
    h->state *= 0x100000001b3ULL;
  }
}

static inline uint64_t splitmix64(uint64_t *s) {
  uint64_t z = (*s += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static inline double now_seconds(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static inline void die(const char *message) {
  fprintf(stderr, "linalg driver: %s\n", message);
  exit(1);
}

/* A matrix as read from SMS: entries in file order, 0-based, values reduced into [0, p). */
typedef struct {
  long rows, cols;
  size_t nnz;
  long *i, *j;
  uint64_t *v;
} triplets_t;

static inline uint64_t reduce_signed(long long x, uint64_t p) {
  long long r = x % (long long)p;
  return (uint64_t)(r < 0 ? r + (long long)p : r);
}

/* Reads `rows cols M` then `i j v` lines until `0 0 0`. Values may be negative or >= p. Values are
 * parsed as unsigned 64-bit when they carry no sign, so a 64-bit prime's residues survive. */
static inline triplets_t read_sms(const char *path, uint64_t p) {
  FILE *f = fopen(path, "r");
  if (!f) die("cannot open the matrix");
  triplets_t t = {0, 0, 0, NULL, NULL, NULL};
  char kind[8];
  if (fscanf(f, "%ld %ld %7s", &t.rows, &t.cols, kind) != 3) die("bad SMS header");
  size_t cap = 1024;
  t.i = (long *)malloc(cap * sizeof(long));
  t.j = (long *)malloc(cap * sizeof(long));
  t.v = (uint64_t *)malloc(cap * sizeof(uint64_t));
  for (;;) {
    long i, j;
    char value[32];
    if (fscanf(f, "%ld %ld %31s", &i, &j, value) != 3) die("truncated SMS body");
    if (i == 0 && j == 0) break;
    if (i < 1 || i > t.rows || j < 1 || j > t.cols) die("SMS index out of range");
    if (t.nnz == cap) {
      cap *= 2;
      t.i = (long *)realloc(t.i, cap * sizeof(long));
      t.j = (long *)realloc(t.j, cap * sizeof(long));
      t.v = (uint64_t *)realloc(t.v, cap * sizeof(uint64_t));
    }
    uint64_t x = value[0] == '-' ? reduce_signed(strtoll(value, NULL, 10), p)
                                 : strtoull(value, NULL, 10) % p;
    t.i[t.nnz] = i - 1;
    t.j[t.nnz] = j - 1;
    t.v[t.nnz] = x;
    t.nnz++;
  }
  fclose(f);
  return t;
}

/* Digest of a dense row-major RREF with pivots at 1; zero rows anywhere are skipped and the
 * nonzero rows are taken in the order given, which for an RREF is increasing pivot column. */
static inline uint64_t rref_digest_dense(const uint64_t *a, long rows, long cols, long stride,
                                         long *rank_out) {
  long rank = 0;
  for (long r = 0; r < rows; r++)
    for (long c = 0; c < cols; c++)
      if (a[r * stride + c]) {
        rank++;
        break;
      }
  fnv_t h;
  fnv_init(&h);
  fnv_word(&h, (uint64_t)rows);
  fnv_word(&h, (uint64_t)cols);
  fnv_word(&h, (uint64_t)rank);
  for (long r = 0; r < rows; r++) {
    uint64_t count = 0;
    for (long c = 0; c < cols; c++) count += a[r * stride + c] != 0;
    if (!count) continue;
    fnv_word(&h, count);
    for (long c = 0; c < cols; c++)
      if (a[r * stride + c]) {
        fnv_word(&h, (uint64_t)c);
        fnv_word(&h, a[r * stride + c]);
      }
  }
  *rank_out = rank;
  return h.state;
}

static inline void print_rref(long rows, long cols, long rank, uint64_t digest, double seconds) {
  printf("rref rows=%ld cols=%ld rank=%ld digest=%016" PRIx64 " seconds=%.6f\n", rows, cols, rank,
         digest, seconds);
  fflush(stdout);
}

static inline void print_mul(long n, uint64_t digest, double seconds) {
  printf("mul n=%ld digest=%016" PRIx64 " seconds=%.6f\n", n, digest, seconds);
  fflush(stdout);
}

/* Fills `out` with n*n residues from the stream. */
static inline void random_square(uint64_t *state, uint64_t p, long n, uint64_t *out) {
  for (long k = 0; k < n * n; k++) out[k] = splitmix64(state) % p;
}

typedef struct {
  int is_rref;
  const char *path;
  long n;
  uint64_t prime, seed;
  int threads, reps;
} args_t;

/* Parses the protocol's arguments, printing `--version` itself. */
static inline args_t parse_args(int argc, char **argv, const char *name, const char *library) {
  args_t a = {0, NULL, 0, 0, 0, 1, 1};
  if (argc == 2 && strcmp(argv[1], "--version") == 0) {
    printf("linalg-%s contract=%d library=\"%s\" cflags=\"%s\"\n", name, LINALG_CONTRACT, library,
           DRIVER_CFLAGS);
    exit(0);
  }
  if (argc == 6 && strcmp(argv[1], "rref") == 0) {
    a.is_rref = 1;
    a.path = argv[2];
    a.prime = strtoull(argv[3], NULL, 10);
    a.threads = atoi(argv[4]);
    a.reps = atoi(argv[5]);
  } else if (argc == 7 && strcmp(argv[1], "mul") == 0) {
    a.n = atol(argv[2]);
    a.prime = strtoull(argv[3], NULL, 10);
    a.seed = strtoull(argv[4], NULL, 10);
    a.threads = atoi(argv[5]);
    a.reps = atoi(argv[6]);
  } else {
    fprintf(stderr,
            "usage: linalg-%s rref <matrix.sms> <prime> <threads> <reps>\n"
            "       linalg-%s mul <n> <prime> <seed> <threads> <reps>\n"
            "       linalg-%s --version\n",
            name, name, name);
    exit(64);
  }
  if (a.prime < 2 || a.threads < 1 || a.reps < 1) die("bad prime, threads or reps");
  return a;
}

#endif
