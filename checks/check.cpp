// Numerical checks in C++ for "Prime primitive roots below every power of p".
// (A) G(p) < p for every prime 3 <= p <= 10^8 (p - 1 factored by trial division);
// (F1) partial sums of sum chi_{-3}(n) Lambda(n) n^{-2} at x = 10^3, 10^5, 10^7;
// (F2) sum_m e(-m/p) sum_{(n,p-1)=1} e(m g^n / p) = -phi(p-1) for p = 101, 1009, 10007.
// Exit status 1 if a check fails.
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdio>
#include <numeric>
#include <vector>

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
  std::printf("%s\n", fails ? "SOME FAILED" : "ALL PASS");
  return fails ? 1 : 0;
}
