// sweep <threads> <passes> [mib]: the m5 arm's fixed DRAM work (protocol §4.2, #1106).
//
// Per thread, three double arrays of `mib` MiB each (default 64: three of them exceed any one
// CCD's 32 MiB L3), first-touched, then exactly `passes` triad passes a[i] = b[i] + 3.0 * c[i].
// A fixed count of work, never a duration, so it costs more time when the bandwidth is shared.
// Threads inherit the caller's affinity: they run on the attempt's CPUs and nowhere else.
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

static long passes;
static size_t n;

static void *work(void *arg) {
  (void)arg;
  volatile double *a = malloc(n * sizeof(double));
  double *b = malloc(n * sizeof(double)), *c = malloc(n * sizeof(double));
  if (!a || !b || !c) {
    perror("sweep: malloc");
    exit(2);
  }
  for (size_t i = 0; i < n; i++) {
    a[i] = 0.0;
    b[i] = 1.0;
    c[i] = 2.0;
  }
  for (long p = 0; p < passes; p++)
    for (size_t i = 0; i < n; i++) a[i] = b[i] + 3.0 * c[i];
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 3) {
    fprintf(stderr, "usage: sweep <threads> <passes> [mib]\n");
    return 64;
  }
  int threads = atoi(argv[1]);
  passes = atol(argv[2]);
  long mib = argc > 3 ? atol(argv[3]) : 64;
  if (threads < 1 || threads > 256 || passes < 0 || mib < 1) return 64;
  n = (size_t)mib * 1024 * 1024 / sizeof(double);
  pthread_t t[256];
  for (int i = 0; i < threads; i++) pthread_create(&t[i], NULL, work, NULL);
  for (int i = 0; i < threads; i++) pthread_join(t[i], NULL);
  return 0;
}
