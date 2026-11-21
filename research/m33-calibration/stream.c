// STREAM-like triad load for calibration condition (c): a[i] = b[i] + s * c[i] on N threads,
// forever. Each thread owns three 64 MiB arrays, far beyond any L3, so the load is DRAM bandwidth.
//   cc -O2 -pthread -o stream stream.c && taskset -c <rest CPUs> ./stream 32
#include <pthread.h>
#include <stdlib.h>

#define LEN (8u << 20)

static void *triad(void *unused) {
  (void)unused;
  volatile double *a = malloc(LEN * sizeof *a);  // volatile: the stores must not be elided
  double *b = malloc(LEN * sizeof *b), *c = malloc(LEN * sizeof *c);
  if (!a || !b || !c) abort();
  for (unsigned i = 0; i < LEN; i++) a[i] = 0, b[i] = 1, c[i] = 2;
  for (;;)
    for (unsigned i = 0; i < LEN; i++) a[i] = b[i] + 3.0 * c[i];
  return NULL;
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 32;
  pthread_t t;
  for (int i = 0; i < n; i++) pthread_create(&t, NULL, triad, NULL);
  pthread_join(t, NULL);
  return 0;
}
