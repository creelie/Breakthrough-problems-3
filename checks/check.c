/* Numerical checks in C for "Vinogradov's conjectures on primitive roots and character sums".
   (A) G(p) < p for every prime 3 <= p <= 2*10^7, with the maximum of G(p);
   (C) psi(m)/2 >= (2m+2)/10 + log(2m+2) for 5000 <= m <= 10^7;
   (D) phi(N) tau(N) >= N for N <= 10^7;
   (G) the unsmoothing identity of Lemma 5.2, in exact integer arithmetic;
   (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
   (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6, in exact rationals;
   (J) |tau|^2 = q and Lemma 6.2 for the quadratic characters modulo primes q <= 3000, and the ratio
       max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
   (K) the bound |r(theta)| < 3 in the proof of Lemma 6.2 on a grid;
   (L) the parameter inequalities in the proof of Proposition 6.5.
   Exit status 1 if a check fails. */
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

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


static int legendre(long long n, long long q) {
  uint64_t r = powmod((uint64_t)(((n % q) + q) % q), (uint64_t)((q - 1) / 2), (uint64_t)q);
  return r == 0 ? 0 : (r == 1 ? 1 : -1);
}

/* chi_-4 for k = 0, the Legendre symbol modulo qs[k] otherwise */
static const long long qs_chi[6] = {4, 3, 5, 7, 101, 997};
static int chi_k(int k, long long n) {
  if (k == 0) return n % 2 == 0 ? 0 : (n % 4 == 1 ? 1 : -1);
  return legendre(n, qs_chi[k]);
}

/* D T(Y/D) = sum_{n <= Y/D} chi(n) (Y - D n) */
static long long DT(int k, long long Y, long long D) {
  long long s = 0;
  for (long long n = 1; n * D <= Y; n++) s += chi_k(k, n) * (Y - D * n);
  return s;
}

static uint64_t rng_state = 12345;
static double rnd(void) {
  rng_state = rng_state * 6364136223846793005ULL + 1442695040888963407ULL;
  return (double)(rng_state >> 11) / 9007199254740992.0;
}

typedef struct { long long n, d; } Q;
static long long gcdll(long long a, long long b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b) { long long t = a % b; a = b; b = t; }
  return a;
}
static Q mk(long long n, long long d) {
  if (d < 0) { n = -n; d = -d; }
  long long g = gcdll(n, d);
  if (g == 0) g = 1;
  Q r = {n / g, d / g};
  return r;
}
static Q qadd(Q a, Q b) { return mk(a.n * b.d + b.n * a.d, a.d * b.d); }
static Q qsub(Q a, Q b) { return mk(a.n * b.d - b.n * a.d, a.d * b.d); }
static Q qmul(Q a, Q b) { return mk(a.n * b.n, a.d * b.d); }
static Q qdiv(Q a, Q b) { return mk(a.n * b.d, a.d * b.n); }
static int qcmp(Q a, Q b) {
  __int128 l = (__int128)a.n * b.d, r = (__int128)b.n * a.d;
  return l < r ? -1 : (l > r ? 1 : 0);
}
static Q qmin(Q a, Q b) { return qcmp(a, b) <= 0 ? a : b; }
static Q qi(long long n) { Q r = {n, 1}; return r; }

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
  /* (G) */
  int okG = 1, casesG = 0;
  const long long D = 84;
  const long long Xs[5] = {84, 210, 1036, 84000, 148140}; /* 1, 5/2, 37/3, 1000, 12345/7 */
  const long long Hs[5] = {28, 84, 294, 3360, 6993};     /* 1/3, 1, 7/2, 40, 333/4 */
  for (int k = 0; k < 6; k++)
    for (int i = 0; i < 5; i++)
      for (int j = 0; j < 5; j++) {
        long long X = Xs[i], H = Hs[j], S = 0, tail = 0;
        for (long long n = 1; n * D <= X; n++) S += chi_k(k, n);
        for (long long n = X / D + 1; n * D <= X + H; n++) tail += chi_k(k, n) * (X + H - D * n);
        long long lhs = DT(k, X + H, D) - DT(k, X, D) - H * S;
        long long at = tail < 0 ? -tail : tail;
        if (lhs != tail || D * at > H * (H + D)) okG = 0;
        casesG++;
      }
  printf("%s G: unsmoothing identity and |tail| <= h(h+1), %d cases, exact\n", okG ? "PASS" : "FAIL",
         casesG);
  fails += !okG;
  /* (H) */
  int okH = 1;
  double worstH = 0;
  for (int it = 0; it < 200000; it++) {
    double x = 1 + 1e6 * rnd(), h = x * rnd(), sg = 0.5 + 1.5 * rnd(), t = -100 + 200 * rnd();
    double complex w = (sg + 1) + t * I;
    double dd = cabs(cexp(w * log(x + h)) - cexp(w * log(x)));
    double b1 = cabs(w) * h * pow(x + h, sg), b2 = 2 * pow(x + h, sg + 1), b = b1 < b2 ? b1 : b2;
    if (dd / b > worstH) worstH = dd / b;
    if (dd > b * (1 + 1e-9)) okH = 0;
    double s0 = 0.5 + 0.5 * rnd(), ee = 0.125 * (1 - rnd()), hh = pow(x, s0);
    if (pow(x + hh, s0) > 2 * hh * (1 + 1e-12) || pow(3 * hh, 1 - 4 * ee) > 3 * hh * (1 + 1e-12) ||
        pow(2 * (x + hh), 4 * ee) > 4 * pow(x, 4 * ee) * (1 + 1e-12))
      okH = 0;
  }
  printf("%s H: kernel and size bounds at 200000 random points, max ratio %.6f\n", okH ? "PASS" : "FAIL",
         worstH);
  fails += !okH;
  /* (I) */
  int okI = 1;
  const Q dls[6] = {{1, 1000000}, {1, 1000}, {1, 7}, {1, 1}, {5, 1}, {1000, 1}};
  const Q c78 = {7, 8}, half = {1, 2}, c18 = {1, 8}, c1000 = {1, 1000}, c2000 = {1, 2000};
  for (int i = 0; i < 6; i++) {
    Q dl = dls[i];
    Q f1 = qmin(qdiv(dl, qi(8)), c2000), a1 = qsub(c78, qmul(qi(2), f1));
    okI &= qcmp(qi(0), f1) < 0 && qcmp(f1, c1000) < 0 && qcmp(qmul(qi(8), f1), dl) <= 0;
    okI &= qcmp(half, a1) <= 0 && qcmp(a1, qi(1)) <= 0 && qcmp(qadd(a1, qmul(qi(2), f1)), c78) == 0;
    okI &= qcmp(qadd(a1, qmul(qi(8), f1)), qadd(c78, dl)) <= 0;
    Q d = qmin(dl, qi(1)), f = qmin(qdiv(d, qi(12)), c2000), ep = qdiv(d, qi(8));
    Q a = qsub(c78, qmul(qi(2), f));
    okI &= qcmp(qi(0), f) < 0 && qcmp(f, c1000) < 0 && qcmp(qi(0), ep) < 0 && qcmp(ep, c18) <= 0;
    okI &= qcmp(half, a) <= 0 && qcmp(qadd(a, qmul(qi(8), f)), qi(1)) <= 0;
    okI &= qcmp(qadd(qadd(a, qmul(qi(8), f)), qmul(qi(4), ep)), qadd(c78, dl)) <= 0;
    okI &= qcmp(qadd(a, qmul(qi(2), f)), c78) == 0;
  }
  const Q etas[4] = {{1, 1000}, {1, 1}, {1000, 1}, {1, 7}};
  const Q thetas[4] = {{875001, 1000000}, {9, 10}, {1, 1}, {15, 16}};
  for (int i = 0; i < 4; i++) {
    Q dc = qdiv(qmul(qsub(thetas[i], c78), etas[i]), qadd(qi(1), etas[i]));
    okI &= qcmp(qi(0), dc) < 0 && qcmp(qadd(qadd(qdiv(dc, etas[i]), c78), dc), thetas[i]) == 0;
  }
  printf("%s I: parameters of Theorems 1.4, 1.5 and Corollary 1.6, exact rationals\n",
         okI ? "PASS" : "FAIL");
  fails += !okI;
  /* (J) */
  {
    enum { NJ = 20000 };
    static char ispJ[NJ + 1];
    static int tab[NJ];
    for (int i = 2; i <= NJ; i++) ispJ[i] = 1;
    for (int i = 2; i * i <= NJ; i++)
      if (ispJ[i])
        for (int j = i * i; j <= NJ; j += i) ispJ[j] = 0;
    int okJ = 1, nJ = 0;
    double worstTau = 0, worstJ = 0;
    for (int q = 3; q <= NJ; q++) {
      if (!ispJ[q]) continue;
      for (int a = 0; a < q; a++) tab[a] = -1;
      tab[0] = 0;
      for (long a = 1; a < q; a++) tab[a * a % q] = 1;
      int run = 0, m = 0;
      for (int n = 1; n < q; n++) {
        run += tab[n];
        if (abs(run) > m) m = abs(run);
      }
      if (q <= 3000) {
        double complex tau = 0;
        for (int a = 1; a < q; a++) tau += tab[a] * cexp(2 * M_PI * I * a / q);
        double rel = fabs(creal(tau * conj(tau)) - q) / q;
        if (rel > worstTau) worstTau = rel;
        double b0 = 0;
        for (int k = 1; k <= q / 2; k++) b0 += 1.0 / k;
        if (m > sqrt(q) * (b0 + 6)) okJ = 0;
        nJ++;
      }
      if (q >= 1000) {
        double r = m / (sqrt(q) * log(log(q)));
        if (r > worstJ) worstJ = r;
      }
    }
    okJ &= worstTau < 1e-9 && worstJ < 2;
    printf("%s J: |tau|^2 = q (max rel. error %.1e) and max|S| <= sqrt(q)(B+6) for %d primes; max ratio for "
           "1000 <= q <= 20000: %.4f\n", okJ ? "PASS" : "FAIL", worstTau, nJ, worstJ);
    fails += !okJ;
  }
  /* (K) */
  {
    double worstK = 0;
    for (int k = 1; k <= 500000; k++)
      for (int s = -1; s <= 1; s += 2) {
        double th = s * k / 1e6;
        double complex r = 1 / (1 - cexp(-2 * M_PI * I * th)) - 1 / (2 * M_PI * I * th);
        if (cabs(r) > worstK) worstK = cabs(r);
      }
    int okK = worstK < 3;
    printf("%s K: |r(theta)| on 10^6 grid points of 0 < |theta| <= 1/2, max %.6f\n", okK ? "PASS" : "FAIL",
           worstK);
    fails += !okK;
  }
  /* (L) */
  {
    const double Ls[8] = {200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9};
    int okL = 1;
    for (int i = 0; i < 8; i++) {
      double L = Ls[i], M = ceil(L), lM = log(M);
      okL &= 4 * lM < L && L * L > 11520 && pow(M, 4) >= 2 && lM >= 1 && lM * lM <= 4 * M;
      double rho = pow(4 * lM, 1.5) / (M * M);
      okL &= rho * (1 + L) <= 128 && 32 * lM * lM / M <= 128;
      double k = (L + 4 * lM + 1e-80) * (2 + 2 * M_PI * pow(M, 4)) / (pow(M, 6) * 200 * lM);
      okL &= L + 4 * lM <= 6 * M && 2 + 2 * M_PI * pow(M, 4) <= 8 * pow(M, 4) && k * (1 + L) <= 1 &&
             200 * lM <= 400 * log(L);
    }
    printf("%s L: parameter inequalities of Proposition 6.5 at 8 values of log q\n", okL ? "PASS" : "FAIL");
    fails += !okL;
  }
  printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
