// Numerical checks in C++ for "Vinogradov's conjectures on primitive roots and character sums".
// (A) G(p) < p for every prime 3 <= p <= 10^8 (p - 1 factored by trial division);
// (F1) partial sums of sum chi_{-3}(n) Lambda(n) n^{-2} at x = 10^3, 10^5, 10^7;
// (F2) sum_m e(-m/p) sum_{(n,p-1)=1} e(m g^n / p) = -phi(p-1) for p = 101, 1009, 10007;
// (G) the unsmoothing identity of Lemma 5.2 in exact rational arithmetic;
// (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
// (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6 in exact rationals;
// (J) |tau|^2 = q and Lemma 6.2 for the quadratic characters modulo primes q <= 3000, and the ratio
//     max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
// (K) the bound |r(theta)| < 3 in the proof of Lemma 6.2 on a grid;
// (L) the parameter inequalities in the proof of Proposition 6.5.
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
  // (L)
  {
    const double pi = std::acos(-1.0);
    bool okL = true;
    for (double L : {200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9}) {
      double M = std::ceil(L), lM = std::log(M);
      okL = okL && 4 * lM < L && L * L > 11520 && std::pow(M, 4) >= 2 && lM >= 1 && lM * lM <= 4 * M;
      double rho = std::pow(4 * lM, 1.5) / (M * M);
      okL = okL && rho * (1 + L) <= 128 && 32 * lM * lM / M <= 128;
      double k = (L + 4 * lM + 1e-80) * (2 + 2 * pi * std::pow(M, 4)) / (std::pow(M, 6) * 200 * lM);
      okL = okL && L + 4 * lM <= 6 * M && 2 + 2 * pi * std::pow(M, 4) <= 8 * std::pow(M, 4) && k * (1 + L) <= 1 &&
            200 * lM <= 400 * std::log(L);
    }
    std::printf("%s L: parameter inequalities of Proposition 6.5 at 8 values of log q\n", okL ? "PASS" : "FAIL");
    fails += !okL;
  }
  std::printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
