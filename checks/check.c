/* Numerical checks in C for "The Pólya–Vinogradov inequality with log log q".
   The checks (A) to (M) of check.py, written independently in C99:
   (A) Lemma 2.1 (Chebyshev's bounds) for x, N <= 10^6;
   (B) Lemma 2.2: lambda_1 = 1, |lambda_d| <= 1 and Q = 1/S for the Selberg weights, and the sieve
       bound for a_n = n(n + 2), in long double (Python and Julia do this in exact rationals);
   (C) Lemmas 3.3, 3.4 and 3.6 on grids and for random polynomials;
   (D) the exponent arithmetic of Section 3 and of the proof of Theorem 1.3(ii), in exact rationals;
   (E) Corollary 3.8: the identity for T(x + h) - T(x), the inequalities used for h = x^(47/50),
       and max |sum_{p<=x} xi(p) log p| / (x^(19/20) log(k+2)) for quadratic xi, x <= 10^6;
   (F) Lemmas 4.2 and 4.3 on random data;
   (G) Lemma 4.4 for characters and random completely multiplicative f;
   (H) Lemma 4.5: prime pairs for X <= 10^5 and even 2 <= h <= 100, the sieve remainders, and
       the fourth moment of G(h);
   (I) the constants and the parameters I, J in the proof of Theorem 4.1;
   (J) Lemma 5.1 for primes q <= 20000 and the bound |r(theta)| < 3;
   (K) Lemma 5.2, the sum of m^(-19/20) in Lemma 5.3, and Proposition 5.4;
   (L) Lemmas 6.2 and 6.3: block counts for primes 101 <= q <= 401 and the inequalities;
   (M) Theorem 1.3: L'/L(1, chi) for every nonprincipal chi modulo the primes q <= 1000 from the
       Hurwitz zeta function at s = 1, and the Euler-Kronecker constants against mpmath.
   Exit status 1 if a check fails. */
#include <complex.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif

#define LIMIT 1000000
#define XL 4000000

static uint32_t *spf;
static uint32_t *pr;
static uint32_t np;

static int isp(long long n) { return n >= 2 && n <= XL && spf[n] == (uint32_t)n; }

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

static uint64_t rng_state = 12345;
static double rnd(void) {
  rng_state = rng_state * 6364136223846793005ULL + 1442695040888963407ULL;
  return (double)(rng_state >> 11) / 9007199254740992.0;
}

static long long gcdll(long long a, long long b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b) { long long t = a % b; a = b; b = t; }
  return a;
}

typedef struct { long long n, d; } Q;
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
static int qcmp(Q a, Q b) {
  __int128 l = (__int128)a.n * b.d, r = (__int128)b.n * a.d;
  return l < r ? -1 : (l > r ? 1 : 0);
}
static Q qi(long long n) { Q r = {n, 1}; return r; }
static Q qf(long long n, long long d) { return mk(n, d); }

static int fails = 0;
static void report(const char *name, int ok, const char *detail) {
  printf("%s %s: %s\n", ok ? "PASS" : "FAIL", name, detail);
  fflush(stdout);
  fails += !ok;
}
static char buf[1024];

/* (A) Lemma 2.1 */
static int checkA(double *w1, double *w2, double *w3) {
  int ok = 1;
  double th = 0, ps = 0, sl = 0, sr = 0;
  *w1 = *w2 = *w3 = 0;
  for (long n = 2; n <= LIMIT; n++) {
    uint32_t p = spf[n];
    long m = n;
    while (m % p == 0) m /= p;
    if (m == 1) {
      ps += log(p);
      if (n == p) {
        th += log(p);
        sl += log(p) / p;
        sr += 1.0 / p;
      }
    }
    *w1 = fmax(*w1, th / (n * log(4)));
    *w2 = fmax(*w2, (ps - th) / (2 * sqrt(n) * log(n)));
    *w3 = fmax(*w3, ps / (4.0 * n));
    ok &= sl <= log(n) + log(4) && sr <= log(log(n)) + 10;
  }
  return ok && *w1 <= 1 && *w2 <= 1 && *w3 <= 1;
}

/* (B) Selberg weights in long double */
typedef long double (*NuP)(int);
static long double nu1(int p) { return 1.0L / p; }
static long double nu2(int p) { return 2.0L / p; }
static long double nu3(int p) { return 1.0L / (p + 1); }
static int nD, Dl[64];
static long double lamD[64], Sg;
static long double nu_of(int d, const int *ps, int k, NuP f) {
  long double r = 1;
  for (int i = 0; i < k; i++)
    if (d % ps[i] == 0) r *= f(ps[i]);
  return r;
}
static long double g_of(int d, const int *ps, int k, NuP f) {
  long double r = 1;
  for (int i = 0; i < k; i++)
    if (d % ps[i] == 0) r *= f(ps[i]) / (1 - f(ps[i]));
  return r;
}
static int omega_of(int d, const int *ps, int k) {
  int c = 0;
  for (int i = 0; i < k; i++) c += d % ps[i] == 0;
  return c;
}
static void selberg(const int *ps, int k, NuP f, long long y) {
  int divs[64], nd = 1;
  divs[0] = 1;
  for (int i = 0; i < k; i++) {
    int m = nd;
    for (int j = 0; j < m; j++) divs[nd++] = divs[j] * ps[i];
  }
  nD = 0;
  for (int i = 0; i < nd; i++)
    if ((long long)divs[i] * divs[i] <= y) Dl[nD++] = divs[i];
  Sg = 0;
  for (int i = 0; i < nD; i++) Sg += g_of(Dl[i], ps, k, f);
  for (int i = 0; i < nD; i++) {
    int d = Dl[i];
    long double tot = 0;
    for (int j = 0; j < nD; j++) {
      long long e = Dl[j];
      if (gcdll(e, d) == 1 && (d * e) * (d * e) <= y) tot += g_of((int)e, ps, k, f);
    }
    lamD[i] = (omega_of(d, ps, k) % 2 ? -1 : 1) * g_of(d, ps, k, f) / (nu_of(d, ps, k, f) * Sg) * tot;
  }
}
static int checkB(int *cases) {
  int ok = 1;
  *cases = 0;
  const int P1[6] = {2, 3, 5, 7, 11, 13}, P2[6] = {3, 5, 7, 11, 13, 17}, P3[5] = {2, 5, 7, 13, 19};
  const int *Ps[3] = {P1, P2, P3};
  const int Ks[3] = {6, 6, 5};
  NuP fs[3] = {nu1, nu2, nu3};
  const long long ys[6] = {1, 4, 30, 200, 3000, 100000};
  for (int c = 0; c < 3; c++)
    for (int iy = 0; iy < 6; iy++) {
      selberg(Ps[c], Ks[c], fs[c], ys[iy]);
      long double Qs = 0;
      for (int i = 0; i < nD; i++)
        for (int j = 0; j < nD; j++) {
          long long l = (long long)Dl[i] / gcdll(Dl[i], Dl[j]) * Dl[j];
          Qs += lamD[i] * lamD[j] * nu_of((int)l, Ps[c], Ks[c], fs[c]);
        }
      ok &= fabsl(lamD[0] - 1) < 1e-15L && fabsl(Qs * Sg - 1) < 1e-12L;
      for (int i = 0; i < nD; i++) ok &= fabsl(lamD[i]) <= 1 + 1e-15L;
      (*cases)++;
    }
  const int Xs[3] = {100, 1000, 10000}, zs[4] = {5, 7, 11, 13}, yz[4] = {30, 60, 150, 200};
  const int sp[5] = {3, 5, 7, 11, 13};
  for (int ix = 0; ix < 3; ix++)
    for (int iz = 0; iz < 4; iz++) {
      int ps[5], k = 0;
      for (int i = 0; i < 5; i++)
        if (sp[i] <= zs[iz]) ps[k++] = sp[i];
      selberg(ps, k, nu2, yz[iz]);
      long long P = 1;
      for (int i = 0; i < k; i++) P *= ps[i];
      int X = Xs[ix], cnt = 0;
      for (long long n = 0; n < X; n++) cnt += gcdll(n * (n + 2), P) == 1;
      long double err = 0;
      for (int d = 1; d <= yz[iz]; d++) {
        if (P % d) continue;
        int kk = omega_of(d, ps, k), c = 0;
        for (long long n = 0; n < X; n++) c += (n * (n + 2)) % d == 0;
        err += powl(3, kk) * fabsl(c - powl(2, kk) * X / d);
      }
      ok &= cnt <= X / Sg + err + 1e-9L;
      (*cases)++;
    }
  return ok;
}

/* (C) Lemmas 3.3, 3.4 and 3.6 */
static int checkC(double *worst) {
  int ok = 1;
  *worst = 0;
  for (int i = 1; i <= 400; i++)
    for (int k = 0; k < 360; k++) {
      double complex w = (i / 800.0) * cexp(I * M_PI * k / 180);
      *worst = fmax(*worst, cabs(clog(1 - w)) / cabs(w));
    }
  ok &= *worst <= 1.5;
  for (int it = 0; it < 400; it++) {
    int deg = 1 + (int)(6 * rnd());
    double complex co[8];
    for (int j = 0; j <= deg; j++) {
      double re = 2 * rnd() - 1, im = 2 * rnd() - 1;
      co[j] = re + im * I;
    }
    double re = 2 * rnd() - 1, im = 2 * rnd() - 1;
    double complex c = re + im * I;
    double R = 0.2 + 2 * rnd();
    double r = R * (0.05 + 0.9 * rnd());
#define HPOL(z, out)                                     \
  do {                                                   \
    double complex zz = (z), pw = 1, acc = 0;            \
    for (int j = 0; j <= deg; j++) { acc += co[j] * pw; pw *= zz; } \
    out = acc;                                           \
  } while (0)
    double complex hc, v;
    HPOL(c, hc);
    double A = -1e300, lhs = 0;
    for (int k = 0; k < 720; k++) {
      HPOL(c + R * cexp(2 * M_PI * I * k / 720), v);
      A = fmax(A, creal(v - hc));
    }
    for (int k = 0; k < 360; k++) {
      HPOL(c + r * cexp(2 * M_PI * I * k / 360), v);
      lhs = fmax(lhs, cabs(v - hc));
    }
    ok &= lhs <= 2 * r / (R - r) * A * (1 + 1e-6) + 1e-12;
  }
  const double qqs[6] = {1, 2, 3, 10, 1000, 1e9}, sigs[5] = {0.5, 0.7, 1.0, 2.0, 5.0};
  for (int a = 0; a < 6; a++)
    for (int k = 0; k <= 4000; k++) {
      double t = pow(10, k / 500.0) - 1, qq = qqs[a];
      ok &= log(2 * qq * (3 + t) * (3 + t)) <= 10 * log(qq + 2) * sqrt(1 + t);
      for (int b = 0; b < 5; b++) {
        double complex s = sigs[b] + t * I;
        ok &= cabs(s * (s + 1)) >= (1 + t) * (1 + t) / 8;
      }
    }
  return ok;
}

/* (D) exponents in exact rationals */
static int checkD(Q *s0) {
  Q delta = qf(1, 2000), a = qsub(qf(7, 8), qf(1, 1000));
  Q sigma0 = qadd(a, qmul(qi(8), delta));
  int ok = qcmp(qi(0), delta) < 0 && qcmp(delta, qf(1, 1000)) < 0 && qcmp(qf(1, 2), a) <= 0 &&
           qcmp(a, qi(1)) <= 0 && qcmp(qadd(a, qmul(qi(2), delta)), qf(7, 8)) == 0;
  ok &= qcmp(sigma0, qadd(qf(7, 8), qf(3, 1000))) == 0 &&
        qcmp(qsub(qadd(qi(1), sigma0), qf(47, 50)), qf(19, 20)) < 0;
  ok &= qcmp(qmul(qi(17), qsub(sigma0, qi(1))), qi(-2)) < 0 &&
        pow(2, 1 + (double)sigma0.n / sigma0.d) <= 4;
  *s0 = sigma0;
  return ok;
}

/* (E) Corollary 3.8 */
static double lamE[3001];
static double Tsum(double y) {
  double s = 0;
  for (int n = 1; n <= (int)floor(y); n++) s += lamE[n] * (y - n);
  return s;
}
static int checkE(int *cases, double *worst) {
  int ok = 1;
  const int qs[3] = {3, 5, 101};
  *cases = 0;
  for (int iq = 0; iq < 3; iq++) {
    int q = qs[iq];
    for (int n = 0; n <= 3000; n++) lamE[n] = 0;
    for (int n = 2; n <= 3000; n++) {
      uint32_t p = spf[n];
      int m = n;
      while (m % p == 0) m /= p;
      if (m == 1) lamE[n] = legendre(n, q) * log(p);
    }
    for (int it = 0; it < 40; it++) {
      double x = 1 + 1400 * rnd();
      double h = x * rnd();
      int fx = (int)floor(x), fxh = (int)floor(x + h);
      double lhs = Tsum(x + h) - Tsum(x), rhs = 0, s = 0;
      for (int n = 1; n <= fx; n++) s += lamE[n];
      rhs = h * s;
      for (int n = fx + 1; n <= fxh; n++) rhs += lamE[n] * (x + h - n);
      ok &= fabs(lhs - rhs) <= 1e-7 * (1 + fabs(lhs)) && fxh - fx <= h + 1;
      (*cases)++;
    }
  }
  for (int k = 0; k <= 6000; k++) {
    double x = pow(10, k / 100.0);
    ok &= log(2 * x) <= 1 + 100 * pow(x, 0.01) && 2 * sqrt(x) * log(x) <= 200 * pow(x, 0.95);
  }
  const int qe[7] = {3, 5, 7, 11, 13, 101, 997};
  *worst = 0;
  for (int iq = 0; iq < 7; iq++) {
    double run = 0;
    for (uint32_t i = 0; i < np && pr[i] <= LIMIT; i++) {
      double p = pr[i];
      run += legendre(pr[i], qe[iq]) * log(p);
      *worst = fmax(*worst, fabs(run) / (pow(p, 0.95) * log(qe[iq] + 2.0)));
    }
  }
  return ok;
}

static double dist1(double x) { return fabs(x - nearbyint(x)); }
static double wM(double M, double th) {
  double d = dist1(th);
  return d < 1 / M ? M : 1 / d;
}
static const double ZETA32 = 2.612375348685488;

/* (F) Lemmas 4.2 and 4.3 */
static int checkF(void) {
  int ok = 1;
  static double ds[1001], ws[1001];
  for (int c = 0; c < 3000; c++) {
    int r = 2 + (int)(400 * rnd());
    int a = (int)(r * rnd());
    while (gcdll(a, r) != 1) a = (a + 1) % r;
    double al = (double)a / r + (2 * rnd() - 1) / ((double)r * r) + (int)(20 * rnd()) - 10;
    for (int k = 1; k <= r / 2; k++) ok &= dist1(k * al) >= 1.0 / (2 * r) - 1e-12;
    int H = (int)(1000 * rnd());
    for (int h = 1; h <= H; h++) ds[h] = dist1(h * al);
    for (int z = 0; z < 3; z++) {
      double t = 0.5 * rnd();
      int cntt = 0;
      for (int h = 1; h <= H; h++) cntt += ds[h] < t;
      ok &= cntt <= (4.0 * H / r + 1) * (4 * r * t + 1);
    }
    double M = 0.5 + 1000 * rnd();
    int K = (int)ceil(log2(M));
    if (K < 0) K = 0;
    double s1 = 0, s2 = 0;
    for (int h = 1; h <= H; h++) {
      ws[h] = ds[h] < 1 / M ? M : 1 / ds[h];
      s1 += ws[h];
      s2 += ws[h] * ws[h];
    }
    ok &= s1 <= (4.0 * H / r + 1) * (3 * M + 4 * r + 8.0 * r * K);
    ok &= s2 <= (4.0 * H / r + 1) * (20 * r * M + 3 * M * M);
  }
  for (int c = 0; c < 2000; c++) {
    double th = 2 * rnd() - 1, U = 0.5 + 300 * rnd();
    int A = (int)(1000 * rnd()), B = A + (int)(U * rnd());
    double complex S = 0;
    for (int x = A + 1; x <= B; x++) S += cexp(2 * M_PI * I * x * th);
    ok &= cabs(S) <= wM(U, th) * (1 + 1e-9);
  }
  for (int c = 0; c < 300; c++) {
    double al = rnd(), U = 1 + 50 * rnd();
    int A = (int)(100 * rnd()), B = A + (int)U, N = (int)(2000 * rnd()) + 1;
    int nv = 1 + (int)(20 * rnd()), V[64], m = 0;
    double complex b[64];
    for (int z = 0; z < nv; z++) {
      int v = 1 + (int)(60 * rnd()), dup = 0;
      for (int y = 0; y < m; y++) dup |= V[y] == v;
      if (!dup) V[m++] = v;
    }
    for (int y = 1; y < m; y++)            /* sort, as the other programs do */
      for (int z = y; z > 0 && V[z - 1] > V[z]; z--) { int t = V[z]; V[z] = V[z - 1]; V[z - 1] = t; }
    for (int y = 0; y < m; y++) {
      double ph = rnd();
      b[y] = cexp(2 * M_PI * I * ph) * rnd();
    }
    double lhs = 0, rhs = 0;
    for (int u = A + 1; u <= B; u++) {
      double complex t = 0;
      for (int y = 0; y < m; y++)
        if ((long long)u * V[y] <= N) t += b[y] * cexp(2 * M_PI * I * u * V[y] * al);
      lhs += creal(t * conj(t));
    }
    for (int y = 0; y < m; y++)
      for (int z = 0; z < m; z++) rhs += cabs(b[y]) * cabs(b[z]) * wM(U, (V[y] - V[z]) * al);
    ok &= lhs <= rhs * (1 + 1e-9) + 1e-9;
    int Hh = (int)(80 * rnd());
    double Mm = 0.5 + 100 * rnd(), l2 = 0, sw = 0;
    for (int x = 1; x <= Hh; x++)
      for (int y = 1; y <= Hh; y++) l2 += wM(Mm, (x - y) * al);
    for (int h = 1; h <= Hh; h++) sw += wM(Mm, h * al);
    ok &= l2 <= Hh * (Mm + 2 * sw) * (1 + 1e-12);
  }
  return ok;
}

/* (G) Lemma 4.4 */
static int checkG(double *worst) {
  int ok = 1;
  static double complex f[3001], fp[3001];
  static int seen[3001];
  const int qs[6] = {3, 5, 7, 11, 101, 997};
  *worst = 0;
  for (int trial = 0; trial < 60; trial++) {
    int N = 2 + (int)(2998 * rnd());
    double al = rnd();
    if (trial % 3 == 0) {
      int q = qs[trial / 3 % 6];
      for (int n = 1; n <= N; n++) f[n] = legendre(n, q);
    } else {
      for (int n = 0; n <= N; n++) seen[n] = 0;
      f[1] = 1;
      for (int n = 2; n <= N; n++) {
        uint32_t p = spf[n];
        if (!seen[p]) {
          seen[p] = 1;
          fp[p] = cexp(2 * M_PI * I * rnd());
          if (trial % 3 == 2) fp[p] *= rnd();
        }
        f[n] = fp[p] * f[n / p];
      }
    }
    double complex S = 0, T = 0;
    for (int n = 1; n <= N; n++) S += f[n] * cexp(2 * M_PI * I * n * al);
    for (int p = 2; p <= N; p++) {
      if (!isp(p)) continue;
      double complex in = 0;
      for (int m = 1; m <= N / p; m++) in += f[m] * cexp(2 * M_PI * I * (double)p * m * al);
      T += log(p) * f[p] * in;
    }
    double err = cabs(S * log(N) - T) / N;
    if (err > *worst) *worst = err;
    ok &= err <= 1 + 4 * ZETA32;
  }
  return ok;
}

/* (H) Lemma 4.5 */
static double Gof(long long h) {
  double g = 1;
  long long n = h;
  while (n > 1) {
    uint32_t p = spf[n];
    g *= (double)p / (p - 1);
    while (n % p == 0) n /= p;
  }
  return g;
}
static int checkH(double *worst, double *worstG) {
  int ok = 1;
  const int XO = 100000;
  *worst = 0;
  for (int h = 2; h <= 100; h += 2) {
    double g2 = Gof(h) * Gof(h);
    int cntp = 0;
    for (int X = 2; X <= XO; X++) {
      int n = X - 1, jump = isp(n) && isp(n + h);
      cntp += jump;
      if (jump || X <= 8) {
        double bd = 400 * g2 * X / (log(X) * log(X)) + 3 * pow(X, 0.6);
        ok &= cntp <= bd;
        if (cntp / bd > *worst) *worst = cntp / bd;
      }
    }
  }
  const int Xs[6] = {1, 2, 7, 100, 1001, 2000}, hs[5] = {2, 4, 6, 30, 98},
            dsv[11] = {1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 1155}, sp[5] = {3, 5, 7, 11, 13};
  for (int a = 0; a < 6; a++)
    for (int b = 0; b < 5; b++)
      for (int c = 0; c < 11; c++) {
        int X = Xs[a], h = hs[b], d = dsv[c];
        if (gcdll(d, h) != 1) continue;
        int k = 0, cn = 0;
        for (int z = 0; z < 5; z++) k += d % sp[z] == 0;
        for (long long n = 0; n < X; n++) cn += (n * (n + h)) % d == 0;
        ok &= fabs(cn - pow(2, k) * X / d) <= pow(2, k) && pow(6, k) <= (double)d * d;
      }
  for (long X = 2; X < 100000; X++) {      /* T = floor(X^(1/20)): (T+1)^20 > X */
    long T = lround(pow((double)X, 0.05));
    for (;;) {
      __int128 p = 1;
      for (int z = 0; z < 20; z++) p *= T;
      if (p <= X) break;
      T--;
    }
    for (;;) {
      __int128 p = 1;
      for (int z = 0; z < 20; z++) p *= T + 1;
      if (p > X) break;
      T++;
    }
    __int128 p = 1;
    for (int z = 0; z < 20; z++) p *= T + 1;
    ok &= p > X;
  }
  for (long m = 1; m < 100000; m++) {      /* tau(m) <= 2^Omega(m) */
    long n = m, tau = 1, Om = 0;
    while (n > 1) {
      uint32_t p = spf[n];
      int e = 0;
      while (n % p == 0) { n /= p; e++; }
      tau *= e + 1;
      Om += e;
    }
    ok &= tau <= (1L << Om);
  }
  double acc = 0;
  *worstG = 0;
  for (int h = 1; h <= XO; h++) {
    double g = Gof(h);
    acc += g * g * g * g;
    if (acc / h > *worstG) *worstG = acc / h;
  }
  ok &= *worstG <= exp(30) && M_PI * M_PI / 6 - 1 <= 1;
  for (__int128 t = 1; t < 100000; t++) ok &= (t + 1) * (t + 1) * (t + 1) * (t + 1) * (t + 1) <= (t + 31) * t * t * t * t;
  return ok;
}

/* (I) constants and parameters in the proof of Theorem 4.1 */
static int checkI(void) {
  int ok = 64 * log(2) < 45;
  for (long long l = 64; l <= 10000; l++) {
    int Ib = 0;
    while ((1LL << Ib) <= l) Ib++;
    long long J = l + 1 - 4 * Ib;
    __int128 p16 = 1;
    for (int z = 0; z < Ib; z++) p16 *= 16;
    __int128 L4 = (__int128)l * l * l * l;
    ok &= p16 > L4 && 1 <= J && J <= l && 4 * Ib <= l && (1LL << Ib) <= 2 * l && J + 4 * Ib == l + 1;
    /* J^2 2^J l^4 <= (l+1)^2 2^(l+1), with 2^(l+1) = 2^J 16^I */
    ok &= (__int128)J * J * L4 <= (__int128)(l + 1) * (l + 1) * p16 && (__int128)(l + 1) * (l + 1) <= L4;
  }
  ok &= 1 / log(2) <= 2;
  double tail = 0;
  for (int j = 0; j < 400; j++) tail += (j + 1.0) * (j + 1.0) * pow(0.75, j);
  ok &= tail > 111.99 && tail <= 112 + 1e-9 && 7.0 / 4 / (1.0 / 64) == 112;
  for (int j = 0; j < 2000; j++) {
    if (j <= 30) {
      __int128 l8 = 1 + 2 * j, r9 = 2 * (__int128)(j + 1) * (j + 1);
      for (int z = 0; z < j; z++) { l8 *= 8; r9 *= 9; }
      ok &= l8 <= r9;
    } else {
      ok &= log(1 + 2.0 * j) + j * log(8) < log(2) + 2 * log(j + 1.0) + j * log(9) - 1;
    }
  }
  for (int J = 1; J < 200; J++) {
    double s = 0;
    for (int j = 0; j < J; j++) s += pow(2, j / 2.0);
    ok &= s <= 3 * pow(2, J / 2.0);
  }
  ok &= 3 * sqrt(14) <= 12 && sqrt(24) <= 5 && 8 * 112 + 12 == 908 && 6 * 225 == 1350 && 1350 <= 37 * 37 &&
        15 + 37 == 52;
  const long long c4[4] = {320LL * 3375, 48LL * 50625, 80LL * 3375, 180LL * 3375};
  for (int z = 0; z < 4; z++) ok &= c4[z] <= 2560000;
  ok &= pow(2, 0.25) <= 2 && pow(2, 0.3) <= 2 && 2 + 16 + 32 * 2 * 3375 == 216018;
  for (int k = 0; k < 3000; k++) {
    double x = 1 + pow(10, k / 10.0);
    ok &= log(x) <= 15 * pow(x, 1.0 / 15) && log(x) <= 4 * pow(x, 0.25);
  }
  double lf = 0;
  for (int N = 1; N < 10000; N++) {
    lf += log(N);
    ok &= N * log(N) - lf <= N;
  }
  double s1 = 0, s2 = 0;
  for (uint32_t i = 0; i < np && pr[i] <= LIMIT; i++) {
    double p = pr[i];
    s1 += log(p) / (p * (p - 1));
    s2 += log(p) / (p * p);
  }
  ok &= s1 <= 2 * s2 && 2 * s2 <= 2 * ZETA32;
  return ok;
}

/* (J) Lemma 5.1 */
static int checkJ(double *worstTau, int *nJ, double *worstJ, double *worstR) {
  static int tab[20001];
  int ok = 1;
  *nJ = 0;
  *worstTau = *worstJ = *worstR = 0;
  for (int q = 3; q <= 20000; q++) {
    if (!isp(q)) continue;
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
      *worstTau = fmax(*worstTau, fabs(creal(tau * conj(tau)) - q) / q);
      double b0 = 0;
      for (int k = 1; k <= q / 2; k++) b0 += 1.0 / k;
      ok &= m <= sqrt(q) * (b0 + 6);
      (*nJ)++;
    }
    if (q >= 1000) *worstJ = fmax(*worstJ, m / (sqrt(q) * log(log(q))));
  }
  for (int k = 1; k <= 500000; k++)
    for (int s = -1; s <= 1; s += 2) {
      double th = s * k / 1e6;
      double complex r = 1 / (1 - cexp(-2 * M_PI * I * th)) - 1 / (2 * M_PI * I * th);
      *worstR = fmax(*worstR, cabs(r));
    }
  return ok && *worstTau < 1e-9 && *worstJ < 2 && *worstR < 3;
}

/* (K) Lemma 5.2, Lemma 5.3, Proposition 5.4 */
static int checkK(double *worstS) {
  int ok = 1;
  double prod = 1;
  *worstS = 0;
  for (long Y = 2; Y <= LIMIT; Y++) {
    if (isp(Y)) prod /= 1 - 1.0 / Y;
    *worstS = fmax(*worstS, prod / (exp(11) * log(Y)));
  }
  ok &= *worstS <= 1;
  double s19 = 0;
  for (long m = 1; m <= 1000000; m++) {
    s19 += pow(m, -0.95);
    if (m % 997 == 0 || m < 100) ok &= s19 <= 20 * pow(m, 0.05);
  }
  const double Ls[8] = {200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9};
  for (int i = 0; i < 8; i++) {
    double L = Ls[i], M = ceil(L), lM = log(M);
    ok &= pow(L / 16, 4) / 24 > L + 1 && L + 1 >= M && 16 * lM < L && pow(M, 16) >= 2 && lM >= 1 && M <= 2 * L;
    double rho = L * L / pow(M, 4);
    ok &= rho * (1 + L) <= 2 / M && 2 / M <= 1;
    double logqR = L + 16 * lM + log1p(2 * exp(-L - 16 * lM));
    ok &= logqR <= 18 * M && 2 + 2 * M_PI * pow(M, 16) <= 8 * pow(M, 16);
    double k = logqR * (2 / pow(M, 16) + 2 * M_PI) / (pow(M, 3) * 700 * lM);
    ok &= k * (1 + L) <= 288 / (700 * M) && 288 / (700 * M) <= 1;
    ok &= 700 <= 700 * lM && 700 * lM <= 1400 * log(L);
  }
  double s1 = 0;
  for (long t = 2; t <= 1000000; t++) {
    s1 += 1 / (t * log(t));
    if (t == 2) ok &= s1 <= 3;
    if (t == 3 || t == 10 || t == 100 || t == 1000 || t == 10000 || t == 100000 || t == 1000000)
      ok &= s1 <= 3 + log(log(t));
  }
  return ok;
}

/* (L) Lemmas 6.2 and 6.3 */
static int is_prime_power(long n) {
  if (isp(n)) return 1;
  uint32_t p = spf[n];
  while (n % p == 0) n /= p;
  return n == 1;
}
static int checkL(int *cases, double *worstB, double *worstN) {
  int ok = 1;
  *cases = 0;
  *worstB = *worstN = 0;
  for (uint32_t i = 0; i < np; i++) {
    long q = pr[i];
    if (q < 101 || q > 401) continue;
    long zz[7] = {2, 3, 5, 10, 30, (long)sqrt((double)q), q - 1}, zs[7];
    while (zz[5] * zz[5] > q) zz[5]--;
    while ((zz[5] + 1) * (zz[5] + 1) <= q) zz[5]++;
    int nz = 0;
    for (int a = 0; a < 7; a++) {
      int dup = 0;
      for (int b = 0; b < nz; b++) dup |= zs[b] == zz[a];
      if (!dup) zs[nz++] = zz[a];
    }
    for (int j = 0; (2L << j) * q <= XL; j++) {
      long M = 1L << j;
      int cnt = 0;
      for (long m = M; m < 2 * M; m++) cnt += is_prime_power(1 + m * q);
      *worstN = fmax(*worstN, cnt / (393.0 * M / (j + 1)));
      ok &= cnt <= 393.0 * M / (j + 1);
      for (int a = 0; a < nz; a++) {
        double z = zs[a], bnd = 2 * M / log(z) + z * (1 + log(z)) * (1 + log(z)) + z;
        *worstB = fmax(*worstB, cnt / bnd);
        ok &= cnt <= bnd;
        (*cases)++;
      }
    }
  }
  for (int k = 0; k <= 200000; k++) {
    double u = 1 + k / 1000.0;
    ok &= (2 + u) * (2 + u) * (32 * u + 1) <= 297 * u * u * u && u * u * u <= pow(2, 3 * u);
    ok &= (1 + u * log(2)) * (1 + u * log(2)) + 1 <= (2 + u) * (2 + u);
  }
  for (long j = 32; j < 100000; j++) ok &= 64 * (j + 1) <= 96 * j * log(2);
  ok &= 50 * log(2) <= 35 && log(25) <= 4 && log(log(3)) > 1.0 / 11;
  ok &= 40 <= 440 * log(log(3)) && 393 == 96 + 297;
  /* J = floor(16 log2 q) + 1 satisfies q^16 < 2^J <= 2 q^16 as long as 16 log2 q is not within
     10^-9 of an integer, which is checked; and J <= 25 log q */
  for (uint32_t i = 1; i < np && pr[i] <= LIMIT; i++) {
    long double x = 16 * log2l((long double)pr[i]), fr = x - floorl(x);
    long J = (long)floorl(x) + 1;
    ok &= fr > 1e-9L && fr < 1 - 1e-9L && J <= 25 * log(pr[i]);
  }
  return ok;
}

/* (M) Theorem 1.3: L'/L(1, chi) = -log q + sum chi(a) gamma_1(a/q) / sum chi(a) psi(a/q) */
static const double B2[8] = {1.0 / 6, -1.0 / 30, 1.0 / 42, -1.0 / 30, 5.0 / 66, -691.0 / 2730, 7.0 / 6,
                             -3617.0 / 510};
static double HARM[20];
#define EM_N 30
static const double EULER = 0.5772156649015329;
static double digam(double a) {
  double x = a + EM_N, s = log(x) - 1 / (2 * x);
  for (int j = 0; j < 8; j++) s -= B2[j] / ((2 * j + 2) * pow(x, 2 * j + 2));
  for (int k = 0; k < EM_N; k++) s -= 1 / (a + k);
  return s;
}
static double stieltjes1(double a) {
  double x = a + EM_N, lx = log(x), s = 0;
  for (int k = 0; k < EM_N; k++) s += log(a + k) / (a + k);
  s += -lx * lx / 2 + lx / (2 * x);
  for (int j = 0; j < 8; j++) s += B2[j] * (lx - HARM[2 * j + 1]) / ((2 * j + 2) * pow(x, 2 * j + 2));
  return s;
}
static int primitive_root(int q) {
  int fs[16], nf = 0, n = q - 1;
  while (n > 1) {
    int p = spf[n];
    fs[nf++] = p;
    while (n % p == 0) n /= p;
  }
  for (int g = 2; g < q; g++) {
    int good = 1;
    for (int i = 0; i < nf; i++) good &= powmod(g, (q - 1) / fs[i], q) != 1;
    if (good) return g;
  }
  return 0;
}
static double complex ek(int q, double *mx) {
  static double ps[1000], g1[1000];
  static double complex roots[1000];
  int g = primitive_root(q);
  uint64_t x = 1;
  for (int k = 0; k < q - 1; k++) {
    ps[k] = digam((double)x / q);
    g1[k] = stieltjes1((double)x / q);
    roots[k] = cexp(2 * M_PI * I * k / (q - 1));
    x = x * g % q;
  }
  double complex tot = 0;
  *mx = 0;
  for (int j = 1; j < q - 1; j++) {
    double complex num = 0, den = 0;
    for (int k = 0; k < q - 1; k++) {
      double complex w = roots[(long)j * k % (q - 1)];
      num += w * g1[k];
      den += w * ps[k];
    }
    double complex r = -log(q) + num / den;
    tot += r;
    *mx = fmax(*mx, cabs(r));
  }
  return EULER + tot;
}
/* gamma_q from mpmath at 90 digits: euler + sum over chi != 1 of L'/L(1, chi), the logarithmic
   derivative taken from the Hurwitz zeta function and its derivative at s = 1 + 10^-25 */
static const int REFQ[9] = {3, 5, 7, 11, 13, 19, 101, 199, 293};
static const double REFV[9] = {0.945497280871680703, 1.72062421251340476, 2.08759407471733013,
                               2.41542590428326783,  2.6107577374176502,  4.79040941571428333,
                               5.29701289150966972,  6.47366513609320739, 3.38438152121953979};
static int checkM(double *lo, double *hi, double *mxr, double *g3, double *g19, double *worstR) {
  HARM[0] = 0;
  for (int n = 1; n < 20; n++) HARM[n] = HARM[n - 1] + 1.0 / n;
  int ok = fabs(digam(1) + EULER) < 1e-13 && fabs(stieltjes1(1) + 0.0728158454836767) < 1e-13;
  ok &= fabs(digam(0.5) + EULER + 2 * log(2)) < 1e-13;
  *lo = 1e9, *hi = -1e9, *mxr = 0, *worstR = 0;
  for (int q = 3; q <= 1000; q++) {
    if (!isp(q)) continue;
    double mx;
    double complex gq = ek(q, &mx);
    ok &= fabs(cimag(gq)) < 1e-9;
    *lo = fmin(*lo, creal(gq) / log(q));
    *hi = fmax(*hi, creal(gq) / log(q));
    *mxr = fmax(*mxr, mx / log(log(q)));
    if (q == 3) *g3 = creal(gq);
    if (q == 19) *g19 = creal(gq);
    for (int i = 0; i < 9; i++)
      if (REFQ[i] == q) *worstR = fmax(*worstR, fabs(creal(gq) - REFV[i]));
  }
  return ok && *worstR < 1e-9;
}

int main(void) {
  spf = calloc(XL + 1, sizeof(uint32_t));
  for (uint32_t i = 2; i <= XL; i++)
    if (!spf[i])
      for (uint64_t j = i; j <= XL; j += i)
        if (!spf[j]) spf[j] = i;
  pr = malloc(sizeof(uint32_t) * 300000);
  np = 0;
  for (uint32_t i = 2; i <= XL; i++)
    if (spf[i] == i) pr[np++] = i;

  double w1, w2, w3;
  int ok = checkA(&w1, &w2, &w3);
  snprintf(buf, sizeof buf, "theta(x) <= x log 4 (max ratio %.4f), psi - theta <= 2 sqrt(x) log x (%.4f), "
           "psi(x) <= 4x (%.4f), (iii) and (iv) for x, N <= 10^6", w1, w2, w3);
  report("A", ok, buf);

  int cases;
  ok = checkB(&cases);
  snprintf(buf, sizeof buf, "lambda_1 = 1, |lambda_d| <= 1, Q = 1/S and the sieve bound in %d cases, long double",
           cases);
  report("B", ok, buf);

  double worst;
  ok = checkC(&worst);
  double A0 = 0;
  for (uint32_t i = 0; i < np && pr[i] <= LIMIT; i++) A0 += pow(pr[i], -1.5);
  snprintf(buf, sizeof buf, "|log(1-w)| <= 1.5|w| on |w| <= 1/2 (max ratio %.4f), A_0 = %.5f; "
           "Borel-Caratheodory for 400 random polynomials; Lemma 3.6 on grids", worst, 1.5 * A0);
  report("C", ok, buf);

  Q s0;
  ok = checkD(&s0);
  snprintf(buf, sizeof buf, "sigma_0 = %lld/%lld = 7/8 + 3/1000, 1 + sigma_0 - 47/50 < 19/20, "
           "17(sigma_0 - 1) < -2, exact", s0.n, s0.d);
  report("D", ok, buf);

  ok = checkE(&cases, &worst);
  snprintf(buf, sizeof buf, "T(x+h) - T(x) identity in %d cases, log(2x) <= 1 + 100 x^(1/100), "
           "2 sqrt(x) log x <= 200 x^(19/20); max |sum xi(p) log p| / (x^(19/20) log(k+2)) = %.4f", cases, worst);
  report("E", ok, buf);

  ok = checkF();
  report("F", ok, "Lemma 4.2 (i)-(iii) for 3000 random (alpha, a/r), Lemma 4.3 (i) at 2000 and (ii), (iii) at "
         "300 random cases");

  ok = checkG(&worst);
  snprintf(buf, sizeof buf, "Lemma 4.4 for 60 completely multiplicative f, N <= 3000: max error / N = %.4f <= "
           "C_5 = %.4f", worst, 1 + 4 * ZETA32);
  report("G", ok, buf);

  double worstG;
  ok = checkH(&worst, &worstG);
  snprintf(buf, sizeof buf, "prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, even "
           "2 <= h <= 100 (max ratio %.4f); |R_d| <= 2^omega(d); tau(m) <= 2^Omega(m); max_X X^-1 sum G(h)^4 = "
           "%.3f <= e^30", worst, worstG);
  report("H", ok, buf);

  ok = checkI();
  double Kb = 80 * sqrt(800 * exp(15)) + 52, C1 = 45 + 1 + 4 * ZETA32 + 908 + 216018 * Kb + 60 + 2 * Kb;
  snprintf(buf, sizeof buf, "constants of Theorem 4.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= "
           "10^4; K_b = %.4e, C_1 = %.4e", Kb, C1);
  report("I", ok, buf);

  double wt, wj, wr;
  int nJ;
  ok = checkJ(&wt, &nJ, &wj, &wr);
  snprintf(buf, sizeof buf, "|tau|^2 = q (max rel. error %.1e) and max|S| <= sqrt(q)(B+6) for %d primes; max "
           "ratio for 1000 <= q <= 20000: %.4f; max |r(theta)| = %.6f < 3", wt, nJ, wj, wr);
  report("J", ok, buf);

  ok = checkK(&worst);
  snprintf(buf, sizeof buf, "prod_(p<=Y) (1-1/p)^-1 <= e^11 log Y for Y <= 10^6 (max ratio %.2e); "
           "sum m^(-19/20) <= 20 M^(1/20); Proposition 5.4 at 8 values of log q", worst);
  report("K", ok, buf);

  double wB, wN;
  ok = checkL(&cases, &wB, &wN);
  snprintf(buf, sizeof buf, "block counts <= sieve bound in %d cases (max ratio %.4f); N_j <= 393 2^j/(j+1) "
           "(max ratio %.4f); the inequalities of Lemma 6.3 on grids and for primes q <= 10^6", cases, wB, wN);
  report("L", ok, buf);

  double lo, hi, mxr, g3 = 0, g19 = 0, wR;
  ok = checkM(&lo, &hi, &mxr, &g3, &g19, &wR);
  snprintf(buf, sizeof buf, "gamma_q for primes 3 <= q <= 1000 is real with %.4f <= gamma_q/log q <= %.4f; "
           "max |L'/L(1,chi)|/log log q = %.4f; gamma_3 = %.12f, gamma_19 = %.12f; 9 values agree with mpmath "
           "to %.1e", lo, hi, mxr, g3, g19, wR);
  report("M", ok, buf);

  printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
