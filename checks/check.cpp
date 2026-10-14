// Numerical checks in C++ for "Vinogradov's conjectures on primitive roots and character sums".
// (A) G(p) < p for every prime 3 <= p <= 10^8 (p - 1 factored by trial division);
// (F1) partial sums of sum chi_{-3}(n) Lambda(n) n^{-2} at x = 10^3, 10^5, 10^7;
// (F2) sum_m e(-m/p) sum_{(n,p-1)=1} e(m g^n / p) = -phi(p-1) for p = 101, 1009, 10007;
// (G) the unsmoothing identity of Lemma 5.2 in exact rational arithmetic;
// (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
// (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6 in exact rationals;
// (J) |tau|^2 = q and Lemma 7.1 for the quadratic characters modulo primes q <= 3000, and the ratio
//     max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
// (K) the bound |r(theta)| < 3 in the proof of Lemma 7.1 on a grid;
// (L) the parameter inequalities in the proof of Proposition 7.4;
// (M) Lemmas 6.2 and 6.3 (spacing of the multiples of alpha, the bilinear bounds) on random data;
// (N) Lemma 6.4 for characters and random completely multiplicative f;
// (O) Lemma 6.5: the prime pair bound for X <= 10^5 and even 0 < |h| <= 100, the sieve
//     remainders |R_d| <= tau(d), and the fourth moment of G(h) for X <= 10^5;
// (P) the numerical constants and the parameters I, J in the proof of Theorem 6.1.
// Exit status 1 if a check fails.
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <numeric>
#include <vector>
#include <algorithm>
#include <cstdlib>

using u64 = std::uint64_t;

static u64 powmod(u64 a, u64 e, u64 m) {
  u64 r = 1 % m;
  a %= m;
  while (e) {
    if (e & 1) r = r * a % m;
    a = a * a % m;
    e >>= 1;
  }
  return r;
}


// Exact rationals with 128-bit numerator and denominator.
struct Frac {
  __int128 n, d;
  Frac(__int128 a = 0, __int128 b = 1) : n(a), d(b) { norm(); }
  void norm() {
    if (d < 0) { n = -n; d = -d; }
    __int128 a = n < 0 ? -n : n, b = d;
    while (b) { __int128 t = a % b; a = b; b = t; }
    if (a > 1) { n /= a; d /= a; }
  }
};
static Frac operator+(Frac a, Frac b) { return Frac(a.n * b.d + b.n * a.d, a.d * b.d); }
static Frac operator-(Frac a, Frac b) { return Frac(a.n * b.d - b.n * a.d, a.d * b.d); }
static Frac operator*(Frac a, Frac b) { return Frac(a.n * b.n, a.d * b.d); }
static Frac operator/(Frac a, Frac b) { return Frac(a.n * b.d, a.d * b.n); }
static bool operator<(Frac a, Frac b) { return a.n * b.d < b.n * a.d; }
static bool operator<=(Frac a, Frac b) { return a.n * b.d <= b.n * a.d; }
static bool operator==(Frac a, Frac b) { return a.n == b.n && a.d == b.d; }
static Frac fmin2(Frac a, Frac b) { return a <= b ? a : b; }
static Frac fabsq(Frac a) { return a.n < 0 ? Frac(-a.n, a.d) : a; }
static long long floorq(Frac a) {
  __int128 q = a.n / a.d;
  if (a.n < 0 && q * a.d != a.n) q--;
  return (long long)q;
}

// Section 6
static double dist1(double x) { return std::fabs(x - std::nearbyint(x)); }
static double wM(double M, double th) {
  double d = dist1(th);
  return d < 1 / M ? M : 1 / d;
}
static const double ZETA32 = 2.612375348685488;
static int legendre_q(long long n, long long q) {
  u64 r = powmod((u64)(((n % q) + q) % q), (u64)((q - 1) / 2), (u64)q);
  return r == 0 ? 0 : (r == 1 ? 1 : -1);
}
static std::vector<int> spf_upto(int n) {
  std::vector<int> spf(n + 1);
  for (int i = 0; i <= n; i++) spf[i] = i;
  for (int i = 2; (long long)i * i <= n; i++)
    if (spf[i] == i)
      for (int j = i * i; j <= n; j += i)
        if (spf[j] == j) spf[j] = i;
  return spf;
}
static double Gof(long long h, const std::vector<int>& spf) {
  double g = 1;
  long long n = h < 0 ? -h : h;
  while (n > 1) {
    int p = spf[n];
    g *= double(p) / (p - 1);
    while (n % p == 0) n /= p;
  }
  return g;
}

int main() {
  const u64 LIM = 100000000ULL;
  std::vector<bool> comp(LIM + 1, false);
  std::vector<u64> primes;
  for (u64 i = 2; i <= LIM; i++) {
    if (comp[i]) continue;
    primes.push_back(i);
    for (u64 j = i * i; j <= LIM; j += i) comp[j] = true;
  }
  int fails = 0;
  // (A)
  bool okA = true;
  u64 cnt = 0, sum = 0, worstg = 0, worstp = 0;
  for (std::size_t k = 1; k < primes.size(); k++) {
    u64 p = primes[k], n = p - 1;
    std::vector<u64> qs;
    for (std::size_t t = 0; primes[t] * primes[t] <= n; t++) {
      u64 q = primes[t];
      if (n % q == 0) {
        qs.push_back((p - 1) / q);
        while (n % q == 0) n /= q;
      }
    }
    if (n > 1) qs.push_back((p - 1) / n);
    u64 g = 0;
    for (std::size_t t = 0; t < k; t++) {
      u64 l = primes[t];
      bool prim = true;
      for (u64 e : qs)
        if (powmod(l, e, p) == 1) { prim = false; break; }
      if (prim) { g = l; break; }
    }
    if (!g) { okA = false; break; }
    cnt++;
    sum += g;
    if (g > worstg) { worstg = g; worstp = p; }
  }
  std::printf("%s A: %llu primes 3..10^8, max G(p) = %llu at p = %llu, sum G(p) = %llu\n",
              okA ? "PASS" : "FAIL", (unsigned long long)cnt, (unsigned long long)worstg,
              (unsigned long long)worstp, (unsigned long long)sum);
  fails += !okA;
  // (F1)
  double s = 0;
  bool okF1 = true;
  u64 marks[3] = {1000, 100000, 10000000}, mi = 0;
  // accumulate in increasing n
  std::vector<double> lam(marks[2] + 1, 0.0);
  for (std::size_t t = 0; t < primes.size() && primes[t] <= marks[2]; t++) {
    u64 q = primes[t];
    double lq = std::log((double)q);
    for (u64 k = q; k <= marks[2]; k *= q) lam[k] = lq;
  }
  for (u64 n = 2; n <= marks[2]; n++) {
    if (lam[n] != 0.0) {
      int c = (n % 3 == 0) ? 0 : (n % 3 == 1 ? 1 : -1);
      s += c * lam[n] / ((double)n * (double)n);
    }
    if (n == marks[mi]) {
      std::printf("     x = %llu: partial sum %.6f\n", (unsigned long long)n, s);
      if (std::fabs(s) < 0.1) okF1 = false;
      mi++;
    }
  }
  std::printf("%s F1: the partial sums stay near -0.1726, not O(1/x)\n", okF1 ? "PASS" : "FAIL");
  fails += !okF1;
  // (F2)
  bool okF2 = true;
  const double PI = std::acos(-1.0);
  for (u64 p : {101ULL, 1009ULL, 10007ULL}) {
    u64 N = p - 1, n = N;
    std::vector<u64> qs;
    for (u64 q = 2; q * q <= n; q++)
      if (n % q == 0) { qs.push_back(N / q); while (n % q == 0) n /= q; }
    if (n > 1) qs.push_back(N / n);
    u64 g = 2;
    for (;; g++) {
      bool prim = true;
      for (u64 e : qs) if (powmod(g, e, p) == 1) { prim = false; break; }
      if (prim) break;
    }
    std::vector<u64> roots;
    for (u64 j = 1; j <= N; j++) if (std::gcd(j, N) == 1) roots.push_back(powmod(g, j, p));
    std::complex<double> total = 0;
    for (u64 m = 1; m < p; m++) {
      std::complex<double> S = 0;
      for (u64 r : roots) S += std::polar(1.0, 2 * PI * (double)((m * r) % p) / (double)p);
      total += std::polar(1.0, -2 * PI * (double)(m % p) / (double)p) * S;
    }
    double phi = (double)roots.size();
    std::printf("     p = %llu: value %.3f, -phi(p-1) = %.0f\n", (unsigned long long)p, total.real(), -phi);
    if (std::abs(total + phi) > 1e-6 * (double)p) okF2 = false;
  }
  std::printf("%s F2: the double sum of [Car18, (7.2)] equals -phi(p-1) at u = 1\n", okF2 ? "PASS" : "FAIL");
  fails += !okF2;
  // (G)
  bool okG = true;
  int casesG = 0;
  std::vector<std::function<int(long long)>> chars;
  chars.push_back([](long long n) { return n % 2 == 0 ? 0 : (n % 4 == 1 ? 1 : -1); });
  for (long long q : {3LL, 5LL, 7LL, 101LL, 997LL})
    chars.push_back([q](long long n) {
      u64 r = powmod((u64)(n % q), (u64)((q - 1) / 2), (u64)q);
      return r == 0 ? 0 : (r == 1 ? 1 : -1);
    });
  std::vector<Frac> xs = {Frac(1), Frac(5, 2), Frac(37, 3), Frac(1000), Frac(12345, 7)};
  std::vector<Frac> hs = {Frac(1, 3), Frac(1), Frac(7, 2), Frac(40), Frac(333, 4)};
  for (auto& chi : chars)
    for (Frac x : xs)
      for (Frac h : hs) {
        auto T = [&](Frac y) {
          Frac s(0);
          for (long long n = 1; n <= floorq(y); n++) s = s + Frac(chi(n)) * (y - Frac(n));
          return s;
        };
        long long S = 0;
        for (long long n = 1; n <= floorq(x); n++) S += chi(n);
        Frac tail(0);
        for (long long n = floorq(x) + 1; n <= floorq(x + h); n++) tail = tail + Frac(chi(n)) * (x + h - Frac(n));
        Frac lhs = T(x + h) - T(x) - h * Frac(S);
        if (!(lhs == tail) || !(fabsq(lhs) <= h * (h + Frac(1)))) okG = false;
        casesG++;
      }
  std::printf("%s G: unsmoothing identity and |tail| <= h(h+1), %d cases, exact\n", okG ? "PASS" : "FAIL", casesG);
  fails += !okG;
  // (H)
  bool okH = true;
  double worstH = 0;
  u64 st = 12345;
  auto rnd = [&]() {
    st = st * 6364136223846793005ULL + 1442695040888963407ULL;
    return (double)(st >> 11) / 9007199254740992.0;
  };
  for (int it = 0; it < 200000; it++) {
    double x = 1 + 1e6 * rnd(), h = x * rnd(), sg = 0.5 + 1.5 * rnd(), t = -100 + 200 * rnd();
    std::complex<double> w(sg + 1, t);
    double dd = std::abs(std::exp(w * std::log(x + h)) - std::exp(w * std::log(x)));
    double b = std::min(std::abs(w) * h * std::pow(x + h, sg), 2 * std::pow(x + h, sg + 1));
    worstH = std::max(worstH, dd / b);
    if (dd > b * (1 + 1e-9)) okH = false;
    double s0 = 0.5 + 0.5 * rnd(), ee = 0.125 * (1 - rnd()), hh = std::pow(x, s0);
    if (std::pow(x + hh, s0) > 2 * hh * (1 + 1e-12) || std::pow(3 * hh, 1 - 4 * ee) > 3 * hh * (1 + 1e-12) ||
        std::pow(2 * (x + hh), 4 * ee) > 4 * std::pow(x, 4 * ee) * (1 + 1e-12))
      okH = false;
  }
  std::printf("%s H: kernel and size bounds at 200000 random points, max ratio %.6f\n", okH ? "PASS" : "FAIL", worstH);
  fails += !okH;
  // (I)
  bool okI = true;
  const Frac c78(7, 8), half(1, 2), c18(1, 8), c1000(1, 1000), c2000(1, 2000), one(1), zero(0);
  for (Frac dl : {Frac(1, 1000000), Frac(1, 1000), Frac(1, 7), Frac(1), Frac(5), Frac(1000)}) {
    Frac f1 = fmin2(dl / Frac(8), c2000), a1 = c78 - Frac(2) * f1;
    okI = okI && zero < f1 && f1 < c1000 && Frac(8) * f1 <= dl && half <= a1 && a1 <= one &&
          a1 + Frac(2) * f1 == c78 && a1 + Frac(8) * f1 <= c78 + dl;
    Frac d = fmin2(dl, one), f = fmin2(d / Frac(12), c2000), ep = d / Frac(8), a = c78 - Frac(2) * f;
    okI = okI && zero < f && f < c1000 && zero < ep && ep <= c18 && half <= a && a + Frac(8) * f <= one &&
          a + Frac(8) * f + Frac(4) * ep <= c78 + dl && a + Frac(2) * f == c78;
  }
  std::vector<std::pair<Frac, Frac>> et = {{Frac(1, 1000), c78 + Frac(1, 1000000)}, {Frac(1), Frac(9, 10)},
                                           {Frac(1000), one}, {Frac(1, 7), Frac(15, 16)}};
  for (auto [eta, theta] : et) {
    Frac dc = (theta - c78) * eta / (one + eta);
    okI = okI && zero < dc && dc / eta + c78 + dc == theta;
  }
  std::printf("%s I: parameters of Theorems 1.4, 1.5 and Corollary 1.6, exact rationals\n", okI ? "PASS" : "FAIL");
  fails += !okI;
  // (J)
  {
    const int NJ = 20000;
    std::vector<char> isp(NJ + 1, 1);
    isp[0] = isp[1] = 0;
    for (int i = 2; i * i <= NJ; i++)
      if (isp[i])
        for (int j = i * i; j <= NJ; j += i) isp[j] = 0;
    bool okJ = true;
    int nJ = 0;
    double worstTau = 0, worstJ = 0;
    const double pi = std::acos(-1.0);
    for (int q = 3; q <= NJ; q++) {
      if (!isp[q]) continue;
      std::vector<int> tab(q, -1);
      tab[0] = 0;
      for (long long a = 1; a < q; a++) tab[a * a % q] = 1;
      int run = 0, m = 0;
      for (int n = 1; n < q; n++) {
        run += tab[n];
        m = std::max(m, std::abs(run));
      }
      if (q <= 3000) {
        std::complex<double> tau = 0;
        for (int a = 1; a < q; a++) tau += double(tab[a]) * std::polar(1.0, 2 * pi * a / q);
        worstTau = std::max(worstTau, std::fabs(std::norm(tau) - q) / q);
        double b0 = 0;
        for (int k = 1; k <= q / 2; k++) b0 += 1.0 / k;
        if (m > std::sqrt(double(q)) * (b0 + 6)) okJ = false;
        nJ++;
      }
      if (q >= 1000) worstJ = std::max(worstJ, m / (std::sqrt(double(q)) * std::log(std::log(double(q)))));
    }
    okJ = okJ && worstTau < 1e-9 && worstJ < 2;
    std::printf("%s J: |tau|^2 = q (max rel. error %.1e) and max|S| <= sqrt(q)(B+6) for %d primes; max ratio for "
                "1000 <= q <= 20000: %.4f\n", okJ ? "PASS" : "FAIL", worstTau, nJ, worstJ);
    fails += !okJ;
  }
  // (K)
  {
    const double pi = std::acos(-1.0);
    const std::complex<double> i2pi(0, 2 * pi);
    double worstK = 0;
    for (int k = 1; k <= 500000; k++)
      for (int s : {1, -1}) {
        double th = s * k / 1e6;
        std::complex<double> r = 1.0 / (1.0 - std::exp(-i2pi * th)) - 1.0 / (i2pi * th);
        worstK = std::max(worstK, std::abs(r));
      }
    std::printf("%s K: |r(theta)| on 10^6 grid points of 0 < |theta| <= 1/2, max %.6f\n", worstK < 3 ? "PASS" : "FAIL",
                worstK);
    fails += !(worstK < 3);
  }
  // (L) Proposition 7.4: M = ceil(L), R = M^16, Y = M^700
  {
    const double pi = std::acos(-1.0);
    bool okL = true;
    for (double L : {200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9}) {
      double M = std::ceil(L), lM = std::log(M);
      okL = okL && std::pow(L / 16, 4) / 24 > L + 1 && L + 1 >= M && 16 * lM < L && std::pow(M, 16) >= 2 &&
            lM >= 1 && M <= 2 * L;
      double rho = L * L / std::pow(M, 4);
      okL = okL && rho * (1 + L) <= 2 / M && 2 / M <= 128;
      double logqR = L + 16 * lM + std::log1p(2 * std::exp(-L - 16 * lM));
      okL = okL && logqR <= 18 * M && 2 + 2 * pi * std::pow(M, 16) <= 8 * std::pow(M, 16);
      double k = logqR * (2 / std::pow(M, 16) + 2 * pi) / (std::pow(M, 3) * 700 * lM);
      okL = okL && k * (1 + L) <= 288 / (700 * M) && 288 / (700 * M) <= 1 && 700 * lM <= 1400 * std::log(L);
    }
    double s1 = 0;
    for (int t = 2; t <= 1000000; t++) {
      s1 += 1 / (t * std::log(double(t)));
      if (t == 2) okL = okL && s1 <= 3;
      if (t == 3 || t == 10 || t == 100 || t == 1000 || t == 10000 || t == 100000 || t == 1000000)
        okL = okL && s1 <= 3 + std::log(std::log(double(t)));
    }
    std::printf("%s L: parameter inequalities of Proposition 7.4 at 8 values of log q; sum_{2<=t<=H} 1/(t log t) <= "
                "3 + log log H for H <= 10^6\n", okL ? "PASS" : "FAIL");
    fails += !okL;
  }
  // (M) Lemma 6.2 (spacing) and Lemma 6.3 (bilinear bounds) on random data
  {
    const double pi = std::acos(-1.0);
    auto ex = [&](double x) { return std::polar(1.0, 2 * pi * x); };
    bool ok = true;
    std::vector<double> ds(1001), ws(1001);
    for (int c = 0; c < 3000; c++) {
      int r = 2 + int(400 * rnd());
      int a = int(r * rnd());
      while (std::gcd(a, r) != 1) a = (a + 1) % r;
      double al = double(a) / r + (2 * rnd() - 1) / (double(r) * r) + int(20 * rnd()) - 10;
      for (int k = 1; k <= r / 2; k++) ok = ok && dist1(k * al) >= 1.0 / (2 * r) - 1e-12;
      int H = int(1000 * rnd());
      for (int h = 1; h <= H; h++) ds[h] = dist1(h * al);
      for (int z = 0; z < 3; z++) {
        double t = 0.5 * rnd();
        int cntt = 0;
        for (int h = 1; h <= H; h++) cntt += ds[h] < t;
        ok = ok && cntt <= (4.0 * H / r + 1) * (4 * r * t + 1);
      }
      double M = 0.5 + 1000 * rnd();
      int K = std::max(0, int(std::ceil(std::log2(M))));
      double sa = 0, sb = 0;
      for (int h = 1; h <= H; h++) {
        ws[h] = ds[h] < 1 / M ? M : 1 / ds[h];
        sa += ws[h];
        sb += ws[h] * ws[h];
      }
      ok = ok && sa <= (4.0 * H / r + 1) * (3 * M + 4 * r + 8.0 * r * K) &&
           sb <= (4.0 * H / r + 1) * (20 * r * M + 3 * M * M);
    }
    for (int c = 0; c < 2000; c++) {
      double th = 2 * rnd() - 1, U = 0.5 + 300 * rnd();
      int A = int(1000 * rnd()), B = A + int(U * rnd());
      std::complex<double> S = 0;
      for (int x = A + 1; x <= B; x++) S += ex(x * th);
      ok = ok && std::abs(S) <= wM(U, th) * (1 + 1e-9);
    }
    for (int c = 0; c < 300; c++) {
      double al = rnd(), U = 1 + 50 * rnd();
      int A = int(100 * rnd()), B = A + int(U), N = int(2000 * rnd()) + 1;
      int nv = 1 + int(20 * rnd());
      std::vector<int> V;
      for (int z = 0; z < nv; z++) {
        int v = 1 + int(60 * rnd());
        if (std::find(V.begin(), V.end(), v) == V.end()) V.push_back(v);
      }
      std::vector<std::complex<double>> b;
      for (size_t y = 0; y < V.size(); y++) {
        std::complex<double> e = ex(rnd());
        b.push_back(e * rnd());
      }
      double lhs = 0, rhs = 0;
      for (int u = A + 1; u <= B; u++) {
        std::complex<double> t = 0;
        for (size_t y = 0; y < V.size(); y++)
          if ((long long)u * V[y] <= N) t += b[y] * ex(double(u) * V[y] * al);
        lhs += std::norm(t);
      }
      for (size_t y = 0; y < V.size(); y++)
        for (size_t z = 0; z < V.size(); z++) rhs += std::abs(b[y]) * std::abs(b[z]) * wM(U, (V[y] - V[z]) * al);
      ok = ok && lhs <= rhs * (1 + 1e-9) + 1e-9;
      int Hh = int(80 * rnd());
      double Mm = 0.5 + 100 * rnd(), l2 = 0, sw = 0;
      for (int x = 1; x <= Hh; x++)
        for (int y = 1; y <= Hh; y++) l2 += wM(Mm, (x - y) * al);
      for (int h = 1; h <= Hh; h++) sw += wM(Mm, h * al);
      ok = ok && l2 <= Hh * (Mm + 2 * sw) * (1 + 1e-12);
    }
    std::printf("%s M: Lemma 6.2 (i)-(iii) for 3000 random (alpha, a/r), Lemma 6.3 (i) at 2000 and (ii), (iii) at "
                "300 random cases\n", ok ? "PASS" : "FAIL");
    fails += !ok;
  }
  // (N) Lemma 6.4
  {
    const double pi = std::acos(-1.0);
    auto ex = [&](double x) { return std::polar(1.0, 2 * pi * x); };
    auto spf = spf_upto(3000);
    const int qs[6] = {3, 5, 7, 11, 101, 997};
    bool ok = true;
    double worst = 0;
    for (int trial = 0; trial < 60; trial++) {
      int N = 2 + int(2998 * rnd());
      double al = rnd();
      std::vector<std::complex<double>> f(N + 1), fp(N + 1);
      std::vector<bool> seen(N + 1, false);
      if (trial % 3 == 0) {
        int q = qs[trial / 3 % 6];
        for (int n = 1; n <= N; n++) f[n] = legendre_q(n, q);
      } else {
        f[1] = 1;
        for (int n = 2; n <= N; n++) {
          int p = spf[n];
          if (!seen[p]) {
            seen[p] = true;
            fp[p] = ex(rnd());
            if (trial % 3 == 2) fp[p] *= rnd();
          }
          f[n] = fp[p] * f[n / p];
        }
      }
      std::complex<double> S = 0, T = 0;
      for (int n = 1; n <= N; n++) S += f[n] * ex(n * al);
      for (int p = 2; p <= N; p++) {
        if (spf[p] != p) continue;
        std::complex<double> in = 0;
        for (int m = 1; m <= N / p; m++) in += f[m] * ex(double(p) * m * al);
        T += std::log(double(p)) * f[p] * in;
      }
      double err = std::abs(S * std::log(double(N)) - T) / N;
      worst = std::max(worst, err);
      ok = ok && err <= 1 + 4 * ZETA32;
    }
    std::printf("%s N: Lemma 6.4 for 60 completely multiplicative f, N <= 3000: max error / N = %.4f <= C5 = %.4f\n",
                ok ? "PASS" : "FAIL", worst, 1 + 4 * ZETA32);
    fails += !ok;
  }
  // (O) Lemma 6.5
  {
    const int XO = 100000;
    auto spf = spf_upto(XO + 200);
    auto isp = [&](long long n) { return n >= 2 && spf[n] == n; };
    bool ok = true;
    double worst = 0, worstG = 0;
    for (int h = -100; h <= 100; h += 2) {
      if (h == 0) continue;
      double g2 = Gof(h, spf) * Gof(h, spf);
      int cntp = 0;
      for (int X = 2; X <= XO; X++) {
        int n = X - 1;
        bool jump = n + h >= 0 && isp(n) && isp(n + h);
        cntp += jump;
        if (jump || X <= 8) {
          double bd = 400 * g2 * X / (std::log(double(X)) * std::log(double(X))) + 3 * std::pow(X, 0.6);
          ok = ok && cntp <= bd;
          worst = std::max(worst, cntp / bd);
        }
      }
    }
    for (int X : {1, 2, 7, 100, 1001, 2000})
      for (int h : {2, 6, 30, 98, -4})
        for (int d : {1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 1155}) {
          if (std::gcd(d, h) != 1) continue;
          int tau = 1, cn = 0;
          for (int p : {3, 5, 7, 11, 13})
            if (d % p == 0) tau *= 2;
          for (int n = 0; n < X; n++) cn += ((long long)n * (n + h)) % d == 0;
          ok = ok && std::fabs(cn - double(tau) * X / d) <= tau;
        }
    for (unsigned long long X = 2; X <= 1000000000000000000ULL; X = X < 100000 ? X + 1 : X * 10) {
      unsigned long long m = (unsigned long long)std::llround(std::pow(double(X), 0.1)) + 2;
      for (;;) {
        unsigned __int128 p10 = 1;
        for (int z = 0; z < 10; z++) p10 *= m;
        if (p10 <= X) break;
        m--;
      }
      unsigned long long T = (unsigned long long)std::sqrt(double(m));
      while ((T + 1) * (T + 1) <= m) T++;
      while (T * T > m) T--;
      unsigned __int128 p20 = 1;
      for (int z = 0; z < 20; z++) p20 *= (T + 1);
      ok = ok && p20 > X;
    }
    double acc = 0;
    for (int h = 1; h <= XO; h++) {
      double g = Gof(h, spf);
      acc += g * g * g * g;
      worstG = std::max(worstG, acc / h);
    }
    const double pi = std::acos(-1.0);
    ok = ok && worstG <= std::exp(30.0) && pi * pi / 6 - 1 <= 1;
    for (__int128 t = 1; t < 100000; t++) ok = ok && (t + 1) * (t + 1) * (t + 1) * (t + 1) * (t + 1) <= (t + 31) * t * t * t * t;
    std::printf("%s O: prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, 0 < |h| <= 100 even "
                "(max ratio %.4f); |R_d| <= tau(d); (T+1)^20 > X; max_X X^-1 sum G(h)^4 = %.3f <= e^30\n",
                ok ? "PASS" : "FAIL", worst, worstG);
    fails += !ok;
  }
  // (P) constants and parameters in the proof of Theorem 6.1
  {
    bool ok = 64 * std::log(2.0) < 45;
    for (long long l = 64; l <= 10000; l++) {
      int Ib = 0;
      while ((1LL << Ib) <= l) Ib++;
      long long J = l + 1 - 4 * Ib;
      __int128 p16 = 1;
      for (int z = 0; z < Ib; z++) p16 *= 16;
      __int128 L4 = (__int128)l * l * l * l;
      ok = ok && p16 > L4 && 1 <= J && J <= l && 4 * Ib <= l && (1LL << Ib) <= 2 * l && J + 4 * Ib == l + 1;
      ok = ok && (__int128)J * J * L4 <= (__int128)(l + 1) * (l + 1) * p16 && (__int128)(l + 1) * (l + 1) <= L4;
    }
    ok = ok && std::log(2.0) >= 0.5;
    double tail = 0;
    for (int j = 0; j < 400; j++) tail += (j + 1.0) * (j + 1.0) * std::pow(0.75, j);
    ok = ok && tail > 111.99 && tail <= 112 + 1e-9 && Frac(7, 4) / (Frac(1, 4) * Frac(1, 4) * Frac(1, 4)) == Frac(112);
    for (int j = 0; j < 2000; j++) {
      if (j <= 30) {
        __int128 l8 = 1 + 2 * j, r9 = 2 * (__int128)(j + 1) * (j + 1);
        for (int z = 0; z < j; z++) { l8 *= 8; r9 *= 9; }
        ok = ok && l8 <= r9;
      } else {
        ok = ok && std::log(1 + 2.0 * j) + j * std::log(8.0) < std::log(2.0) + 2 * std::log(j + 1.0) + j * std::log(9.0) - 1;
      }
    }
    for (int J = 1; J < 200; J++) {
      double s = 0;
      for (int j = 0; j < J; j++) s += std::pow(2.0, j / 2.0);
      ok = ok && s <= 3 * std::pow(2.0, J / 2.0);
    }
    ok = ok && 3 * std::sqrt(14.0) <= 12 && std::sqrt(24.0) <= 5 && 8 * 112 + 12 == 908 && 6 * 225 == 1350 &&
         1350 <= 37 * 37 && 15 + 37 == 52;
    for (long long c : {320LL * 3375, 48LL * 50625, 80LL * 3375, 180LL * 3375}) ok = ok && c <= 2560000;
    ok = ok && std::pow(2.0, 0.25) <= 2 && std::pow(2.0, 0.3) <= 2 && 2 + 16 + 32 * 2 * 3375 == 216018;
    for (int k = 0; k < 3000; k++) {
      double x = 1 + std::pow(10.0, k / 10.0);
      ok = ok && std::log(x) <= 15 * std::pow(x, 1.0 / 15) && std::log(x) <= 4 * std::pow(x, 0.25);
    }
    double lf = 0;
    for (int N = 1; N < 10000; N++) {
      lf += std::log(double(N));
      ok = ok && N * std::log(double(N)) - lf <= N;
    }
    double s1 = 0, s2 = 0;
    for (u64 p : primes) {
      if (p > 1000000) break;
      double q = double(p);
      s1 += std::log(q) / (q * (q - 1));
      s2 += std::log(q) / (q * q);
    }
    ok = ok && s1 <= 2 * s2 && 2 * s2 <= 2 * ZETA32;
    double Kb = 80 * std::sqrt(800 * std::exp(15.0)) + 52, C1 = 45 + 1 + 4 * ZETA32 + 908 + 216018 * Kb + 60 + 2 * Kb;
    std::printf("%s P: constants of Theorem 6.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; K_b = "
                "%.4e, C_1 = %.4e\n", ok ? "PASS" : "FAIL", Kb, C1);
    fails += !ok;
  }
  std::printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
