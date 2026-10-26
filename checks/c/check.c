/* Checks for "The Pólya–Vinogradov inequality with log log q for all but q^epsilon characters".
 *
 * (1) Lemma 2.1 (Chebyshev): theta(x) <= x log 4, psi(x) <= 2x and sum_{n<=x} Lambda(n)/n <= log x + 3
 *     for x <= 10^7, by a sieve;
 * (2) the parameters (3.1) and the inequalities (3.2) for theta = 1/2 + j/10^6, j < 5 * 10^5, in double
 *     precision with a margin of 10^-12, and A_theta >= 288;
 * (3) the arithmetic of the proof of Proposition 5.5 and the count (6.1) for L = log q on
 *     [200, 10^5] in steps of 1/100;
 * (4) the sizes: for the quadratic character modulo every prime q with 10^4 <= q <= 10^5,
 *     M(chi) = max_x |sum_{n<=x} (n/q)| against sqrt(q) log q (the Pólya bound) and the largest
 *     ratios M(chi)/sqrt(q) and M(chi)/(sqrt(q) log log q), by the Legendre symbol from a table of
 *     squares; and the bound M(chi) <= (7 + log q) sqrt(q) of Section 6.
 * Prints one line per check and exits with status 1 if any fails. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
static void report(const char *name, int ok, const char *detail) {
    printf("%s %s: %s\n", ok ? "PASS" : "FAIL", name, detail);
    fflush(stdout);
    if (!ok) failures++;
}

int main(void) {
    char buf[512];
    /* (1) Chebyshev */
    const long N = 10000000L;
    unsigned char *comp = calloc(N + 1, 1);
    for (long i = 2; i * i <= N; i++)
        if (!comp[i]) for (long j = i * i; j <= N; j += i) comp[j] = 1;
    double *lam = calloc(N + 1, sizeof(double));
    for (long p = 2; p <= N; p++) if (!comp[p]) { double lp = log((double)p); for (long pk = p; pk <= N; pk *= p) { lam[pk] = lp; if (pk > N / p) break; } }
    double th = 0, ps = 0, sl = 0, w1 = 0, w2 = 0, w3 = -1e9;
    for (long n = 2; n <= N; n++) {
        ps += lam[n]; sl += lam[n] / n; if (!comp[n]) th += log((double)n);
        double a = th / (n * log(4.0)), b = ps / (2.0 * n), c = sl - log((double)n);
        if (a > w1) w1 = a; if (b > w2) w2 = b; if (c > w3) w3 = c;
    }
    snprintf(buf, sizeof buf, "theta(x)/(x log 4) <= %.4f, psi(x)/(2x) <= %.4f, max(sum Lambda(n)/n - log x) = %.4f <= 3, x <= %ld",
             w1, w2, w3, N);
    report("1", w1 <= 1 && w2 <= 1 && w3 <= 3, buf);
    free(lam);

    /* (2) parameters */
    int ok = 1; long minA = 1L << 40;
    for (long j = 0; j < 500000; j++) {
        double t = 0.5 + j / 1e6;
        double d = fmin(1.0 / 2000, (1 - t) / 100), a = fmax(0.5, t - 2 * d), s = a + 8 * d, eta = (1 - s) / 4;
        long A = (long)ceil(36 / eta);
        if (!(t < s - 1e-12 && s < 1 - 1e-12 && 1 - s >= (1 - t) / 2 - 1e-12 && (1 - t) / 8 <= eta + 1e-12 && eta <= 0.125 + 1e-12)) ok = 0;
        if (!(s - 2 * d > t)) ok = 0;
        if (A < minA) minA = A;
    }
    snprintf(buf, sizeof buf, "(3.2) holds for theta = 1/2 + j/10^6, j < 5*10^5; least A_theta = %ld >= 288", minA);
    report("2", ok && minA >= 288, buf);

    /* (3) Proposition 5.5 and (6.1) */
    ok = 1;
    for (long i = 20000; i <= 10000000L; i++) {
        double L = i / 100.0, M = ceil(L), lM = log(M);
        if (!(L / 16 >= log(pow(L / 16, 4) / 24) && pow(L / 16, 4) / 24 > L + 1 && L + 1 >= M)) ok = 0;
        if (!(16 * lM < L)) ok = 0;                                   /* R < q */
        double rho = L * L / pow(M, 4);
        if (!(rho * (1 + L) <= 2 / M && 2 / M <= 1)) ok = 0;
        if (!(L + 16 * lM + 1e-9 <= 18 * M)) ok = 0;                 /* log(qR+2) <= 18 M */
        if (!(2 + 2 * M_PI * pow(M, 16) <= 8 * pow(M, 16))) ok = 0;
        double kb = 288 / (M * M * lM);                              /* 288 M^34 / (M^36 log M) */
        if (!(kb <= 1)) ok = 0;
        if (!(lM <= 2 * log(L) && log(L) >= 1)) ok = 0;
        double eps[4] = {1, 0.5, 0.1, 0.01};
        for (int e = 0; e < 4; e++) {
            double lR = 16 * lM, lhs = 2 * lR + eps[e] / 4 * (log(5.0) + 3 * L + lR) + 9 * log(log(5.0) + 3 * L + lR);
            double rhs = 37 * log(2.0) + 9 * log(20.0) + 45 * log(L) + 3 * eps[e] * L / 4;
            if (!(lhs <= rhs + 1e-9)) ok = 0;
        }
    }
    report("3", ok, "the inequalities of Proposition 5.5 and the reduction (6.1) hold for L in [200, 10^5] (step 1/100), eps in {1, 1/2, 1/10, 1/100}");

    /* (4) quadratic characters */
    ok = 1; double bm = 0, bml = 0; long bq = 0; int cnt = 0;
    signed char *chi = malloc(100001);
    for (long q = 10000; q <= 100000; q++) {
        if (comp[q]) continue;
        memset(chi, -1, q); chi[0] = 0;
        for (long x = 1; x < q; x++) chi[(x * x) % q] = 1;
        long acc = 0, m = 0;
        for (long n = 1; n < q; n++) { acc += chi[n]; if (labs(acc) > m) m = labs(acc); }
        double sq = sqrt((double)q), r = m / sq;
        if (!(m < sq * log((double)q))) ok = 0;
        if (!(m <= (7 + log((double)q)) * sq)) ok = 0;
        if (r > bm) { bm = r; bq = q; }
        if (r / log(log((double)q)) > bml) bml = r / log(log((double)q));
        cnt++;
    }
    snprintf(buf, sizeof buf, "%d primes 10^4 <= q <= 10^5: max M(chi)/sqrt q = %.4f at q = %ld, max M(chi)/(sqrt q log log q) = %.4f; all below sqrt q log q and (7 + log q) sqrt q",
             cnt, bm, bq, bml);
    report("4", ok, buf);
    free(chi); free(comp);
    printf("%s\n", failures ? "FAILED" : "ALL PASS");
    return failures ? 1 : 0;
}
