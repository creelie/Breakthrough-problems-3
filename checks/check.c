/* Numerical checks in C for "The Pólya–Vinogradov inequality with log log q".
   (A) G(p) < p for every prime 3 <= p <= 2*10^7, with the maximum of G(p);
   (C) psi(m)/2 >= (2m+2)/10 + log(2m+2) for 5000 <= m <= 10^7;
   (D) phi(N) tau(N) >= N for N <= 10^7;
   (G) the unsmoothing identity of Lemma 5.2, in exact integer arithmetic;
   (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
   (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6, in exact rationals;
   (J) |tau|^2 = q and Lemma 7.1 for the quadratic characters modulo primes q <= 3000, and the ratio
       max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
   (K) the bound |r(theta)| < 3 in the proof of Lemma 7.1 on a grid;
   (L) the parameter inequalities in the proof of Proposition 7.4;
   (M) Lemmas 6.2 and 6.3 (spacing of the multiples of alpha, the bilinear bounds) on random data;
   (N) Lemma 6.4 for characters and random completely multiplicative f;
   (O) Lemma 6.5: the prime pair bound for X <= 10^5 and even 0 < |h| <= 100, the sieve
       remainders |R_d| <= tau(d), and the fourth moment of G(h) for X <= 10^5;
   (P) the numerical constants and the parameters I, J in the proof of Theorem 6.1.
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

/* Section 6 */
static double dist1(double x) { return fabs(x - nearbyint(x)); }
static double wM(double M, double th) {
  double d = dist1(th);
  return d < 1 / M ? M : 1 / d;
}
static const double ZETA32 = 2.612375348685488;
static double Gof(long long h) {
  double g = 1;
  long long n = h < 0 ? -h : h;
  while (n > 1) {
    uint32_t p = spf[n];
    g *= (double)p / (p - 1);
    while (n % p == 0) n /= p;
  }
  return g;
}
static int isp(long long n) { return n >= 2 && spf[n] == (uint32_t)n; }

static int checkM(void) {
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
    for (int y = 0; y < m; y++) b[y] = cexp(2 * M_PI * I * rnd()) * rnd();
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

static int checkN(double *worst) {
  int ok = 1;
  static double complex f[3001];
  static double complex fp[3001];
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

static int checkO(double *worst, double *worstG) {
  int ok = 1;
  const int XO = 100000;
  *worst = 0;
  for (int h = -100; h <= 100; h += 2) {
    if (h == 0) continue;
    double g2 = Gof(h) * Gof(h);
    int cntp = 0;
    for (int X = 2; X <= XO; X++) {
      int n = X - 1, jump = n + h >= 0 && isp(n) && isp(n + h);
      cntp += jump;
      if (jump || X <= 8) {
        double bd = 400 * g2 * X / (log(X) * log(X)) + 3 * pow(X, 0.6);
        ok &= cntp <= bd;
        if (cntp / bd > *worst) *worst = cntp / bd;
      }
    }
  }
  const int Xs[6] = {1, 2, 7, 100, 1001, 2000}, hs[5] = {2, 6, 30, 98, -4},
            dsv[11] = {1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 1155}, sp[5] = {3, 5, 7, 11, 13};
  for (int a = 0; a < 6; a++)
    for (int b = 0; b < 5; b++)
      for (int c = 0; c < 11; c++) {
        int X = Xs[a], h = hs[b], d = dsv[c];
        if (gcdll(d, h) != 1) continue;
        int tau = 1, cn = 0;
        for (int z = 0; z < 5; z++)
          if (d % sp[z] == 0) tau *= 2;
        for (int n = 0; n < X; n++) cn += ((long long)n * (n + h)) % d == 0;
        ok &= fabs(cn - (double)tau * X / d) <= tau;
      }
  for (unsigned long long X = 2; X <= 1000000000000000000ULL; X = X < 100000 ? X + 1 : X * 10) {
    unsigned long long m = (unsigned long long)llround(pow((double)X, 0.1)) + 2;
    for (;;) {
      unsigned __int128 p10 = 1;
      for (int z = 0; z < 10; z++) p10 *= m;
      if (p10 <= X) break;
      m--;
    }
    unsigned long long T = (unsigned long long)sqrt((double)m);
    while ((T + 1) * (T + 1) <= m) T++;
    while (T * T > m) T--;
    unsigned __int128 p20 = 1;
    for (int z = 0; z < 20; z++) p20 *= (T + 1);
    ok &= p20 > X;
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

static int checkP(uint32_t *pr, uint32_t np) {
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
  ok &= log(2) >= 0.5;
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
  for (uint32_t i = 0; i < np && pr[i] <= 1000000; i++) {
    double p = pr[i];
    s1 += log(p) / (p * (p - 1));
    s2 += log(p) / (p * p);
  }
  ok &= s1 <= 2 * s2 && 2 * s2 <= 2 * ZETA32;
  return ok;
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
  /* (L) Proposition 7.4: M = ceil(L), R = M^16, Y = M^700 */
  {
    const double Ls[8] = {200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9};
    int okL = 1;
    for (int i = 0; i < 8; i++) {
      double L = Ls[i], M = ceil(L), lM = log(M);
      okL &= pow(L / 16, 4) / 24 > L + 1 && L + 1 >= M && 16 * lM < L && pow(M, 16) >= 2 && lM >= 1 && M <= 2 * L;
      double rho = L * L / pow(M, 4);
      okL &= rho * (1 + L) <= 2 / M && 2 / M <= 128;
      double logqR = L + 16 * lM + log1p(2 * exp(-L - 16 * lM));
      okL &= logqR <= 18 * M && 2 + 2 * M_PI * pow(M, 16) <= 8 * pow(M, 16);
      double k = logqR * (2 / pow(M, 16) + 2 * M_PI) / (pow(M, 3) * 700 * lM);
      okL &= k * (1 + L) <= 288 / (700 * M) && 288 / (700 * M) <= 1 && 700 * lM <= 1400 * log(L);
    }
    double s1 = 0;
    for (int t = 2; t <= 1000000; t++) {
      s1 += 1 / (t * log(t));
      if (t == 2) okL &= s1 <= 3;
      if (t == 3 || t == 10 || t == 100 || t == 1000 || t == 10000 || t == 100000 || t == 1000000)
        okL &= s1 <= 3 + log(log(t));
    }
    printf("%s L: parameter inequalities of Proposition 7.4 at 8 values of log q; sum_{2<=t<=H} 1/(t log t) <= "
           "3 + log log H for H <= 10^6\n", okL ? "PASS" : "FAIL");
    fails += !okL;
  }
  /* (M) */
  {
    int okM = checkM();
    printf("%s M: Lemma 6.2 (i)-(iii) for 3000 random (alpha, a/r), Lemma 6.3 (i) at 2000 and (ii), (iii) at 300 "
           "random cases\n", okM ? "PASS" : "FAIL");
    fails += !okM;
  }
  /* (N) */
  {
    double worstN;
    int okN = checkN(&worstN);
    printf("%s N: Lemma 6.4 for 60 completely multiplicative f, N <= 3000: max error / N = %.4f <= C5 = %.4f\n",
           okN ? "PASS" : "FAIL", worstN, 1 + 4 * ZETA32);
    fails += !okN;
  }
  /* (O) */
  {
    double worstO, worstGO;
    int okO = checkO(&worstO, &worstGO);
    printf("%s O: prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, 0 < |h| <= 100 even (max "
           "ratio %.4f); |R_d| <= tau(d); (T+1)^20 > X; max_X X^-1 sum G(h)^4 = %.3f <= e^30\n",
           okO ? "PASS" : "FAIL", worstO, worstGO);
    fails += !okO;
  }
  /* (P) */
  {
    int okP = checkP(pr, np);
    double Kb = 80 * sqrt(800 * exp(15)) + 52, C1 = 45 + 1 + 4 * ZETA32 + 908 + 216018 * Kb + 60 + 2 * Kb;
    printf("%s P: constants of Theorem 6.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; K_b = "
           "%.4e, C_1 = %.4e\n", okP ? "PASS" : "FAIL", Kb, C1);
    fails += !okP;
  }
  printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
