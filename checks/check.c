/* Numerical checks in C for "Prime primitive roots below every power of p".
   (A) G(p) < p for every prime 3 <= p <= 2*10^7, with the maximum of G(p);
   (C) psi(m)/2 >= (2m+2)/10 + log(2m+2) for 5000 <= m <= 10^7;
   (D) phi(N) tau(N) >= N for N <= 10^7.
   Exit status 1 if a check fails. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define LIM 20000000u

static uint32_t *spf;

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
  uint64_t r = 1 % m;
  a %= m;
  while (e) {
    if (e & 1) r = r * a % m;
    a = a * a % m;
    e >>= 1;
  }
  return r;
}

int main(void) {
  int fails = 0;
  spf = calloc(LIM + 1, sizeof(uint32_t));
  for (uint32_t i = 2; i <= LIM; i++)
    if (!spf[i])
      for (uint64_t j = i; j <= LIM; j += i)
        if (!spf[j]) spf[j] = i;
  /* (A) */
  uint32_t *pr = malloc(sizeof(uint32_t) * 1300000);
  uint32_t np = 0;
  for (uint32_t i = 2; i <= LIM; i++)
    if (spf[i] == i) pr[np++] = i;
  uint64_t sum = 0, cnt = 0, worstg = 0, worstp = 0;
  int okA = 1;
  for (uint32_t k = 1; k < np; k++) {
    uint32_t p = pr[k], n = p - 1, qs[16], nq = 0;
    while (n > 1) {
      uint32_t q = spf[n];
      qs[nq++] = (p - 1) / q;
      while (n % q == 0) n /= q;
    }
    uint32_t g = 0;
    for (uint32_t t = 0; t < k; t++) {
      uint32_t l = pr[t];
      int prim = 1;
      for (uint32_t i = 0; i < nq; i++)
        if (powmod(l, qs[i], p) == 1) { prim = 0; break; }
      if (prim) { g = l; break; }
    }
    if (!g) { okA = 0; break; }
    sum += g;
    cnt++;
    if (g > worstg) { worstg = g; worstp = p; }
  }
  printf("%s A: %llu primes 3..%u, max G(p) = %llu at p = %llu, sum G(p) = %llu\n",
         okA ? "PASS" : "FAIL", (unsigned long long)cnt, LIM, (unsigned long long)worstg,
         (unsigned long long)worstp, (unsigned long long)sum);
  fails += !okA;
  /* (C) */
  int okC = 1;
  double psi = 0, least = 1e300;
  for (uint32_t m = 1; m <= 10000000u; m++) {
    if (m > 1) {
      uint32_t q = spf[m], n = m;
      while (n % q == 0) n /= q;
      if (n == 1) psi += log((double)q);
    }
    if (m >= 5000) {
      double margin = psi / 2 - ((2.0 * m + 2) / 10 + log(2.0 * m + 2));
      if (margin < least) least = margin;
      if (margin < 0) okC = 0;
    }
  }
  printf("%s C: psi(m)/2 - (2m+2)/10 - log(2m+2) >= 0 for 5000 <= m <= 10^7, least margin %.3f\n",
         okC ? "PASS" : "FAIL", least);
  fails += !okC;
  /* (D) */
  int okD = 1;
  for (uint32_t N = 1; N <= 10000000u; N++) {
    uint64_t phi = N, tau = 1;
    uint32_t n = N;
    while (n > 1) {
      uint32_t q = spf[n], e = 0;
      while (n % q == 0) { n /= q; e++; }
      phi = phi / q * (q - 1);
      tau *= e + 1;
    }
    if (phi * tau < N) { okD = 0; break; }
  }
  printf("%s D: phi(N) tau(N) >= N for N <= 10^7\n", okD ? "PASS" : "FAIL");
  fails += !okD;
  printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
