/* p(n) mod ell for n <= NMAX by Euler's pentagonal recurrence; writes raw uint8 to stdout. */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  long N = atol(argv[1]); int M = atoi(argv[2]);
  unsigned char *p = malloc(N + 1); p[0] = 1;
  long ng = 0; long *g = malloc(sizeof(long) * 20000); int *sg = malloc(sizeof(int) * 20000);
  for (long k = 1; k * (3 * k - 1) / 2 <= N; k++) {
    g[ng] = k * (3 * k - 1) / 2; sg[ng++] = (k % 2) ? 1 : -1;
    g[ng] = k * (3 * k + 1) / 2; sg[ng++] = (k % 2) ? 1 : -1;
  }
  for (long n = 1; n <= N; n++) {
    long t = 0;
    for (long i = 0; i < ng && g[i] <= n; i++) t += sg[i] * p[n - g[i]];
    t %= M; if (t < 0) t += M; p[n] = (unsigned char)t;
  }
  fwrite(p, 1, N + 1, stdout); return 0;
}
