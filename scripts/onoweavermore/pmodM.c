/* p(n) mod M (M = 13*17*19*23*29*31) for n <= N, Euler pentagonal recurrence; raw uint32 to file. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  long N = atol(argv[1]); const int64_t M = 13LL*17*19*23*29*31;
  uint32_t *p = malloc(sizeof(uint32_t) * (N + 1)); p[0] = 1;
  long ng = 0; long *g = malloc(sizeof(long) * 40000); int *sg = malloc(sizeof(int) * 40000);
  for (long k = 1; k * (3 * k - 1) / 2 <= N; k++) {
    g[ng] = k * (3 * k - 1) / 2; sg[ng++] = (k % 2) ? 1 : -1;
    g[ng] = k * (3 * k + 1) / 2; sg[ng++] = (k % 2) ? 1 : -1;
  }
  for (long n = 1; n <= N; n++) {
    int64_t t = 0;
    for (long i = 0; i < ng && g[i] <= n; i++) t += sg[i] * (int64_t)p[n - g[i]];
    t %= M; if (t < 0) t += M; p[n] = (uint32_t)t;
  }
  FILE *f = fopen(argv[2], "wb"); fwrite(p, sizeof(uint32_t), N + 1, f); fclose(f); return 0;
}
