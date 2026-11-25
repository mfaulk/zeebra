// hbusy <threads> <seconds>: spin that many threads for that long (H-A3 harness-cost child).
#include <pthread.h>
#include <stdlib.h>
#include <time.h>

static double secs;
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}
static void *spin(void *arg) {
  (void)arg;
  double end = now() + secs;
  volatile unsigned long x = 0;
  while (now() < end)
    for (int i = 0; i < 10000; i++) x += i;
  return NULL;
}
int main(int argc, char **argv) {
  int n = atoi(argv[1]);
  secs = atof(argv[2]);
  pthread_t t[256];
  for (int i = 0; i < n; i++) pthread_create(&t[i], NULL, spin, NULL);
  for (int i = 0; i < n; i++) pthread_join(t[i], NULL);
  return 0;
}
