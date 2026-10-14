#!/usr/bin/env python3
"""Numerical checks for "Prime primitive roots below every power of p".

(A) least prime primitive root G(p) < p for every prime 3 <= p <= LIMIT;
(B) the character identity of Lemma 3.1 for every prime p <= 200 and 0 <= n < 3p;
(C) psi(m)/2 >= (2m+2)/10 + log(2m+2) for 5000 <= m <= M_LIMIT (Lemma 3.3);
(D) phi(N)/N >= 1/tau(N) for 1 <= N <= 10^6 (Lemma 3.2);
(E) the exponent arithmetic of Section 4, in exact rationals;
(F) the two computations of Remark 1.7 on Carella's estimates.
Prints one line per check and exits with status 1 if any check fails.
"""
import cmath
import math
import sys
from fractions import Fraction

LIMIT = 10**6
M_LIMIT = 10**6


def sieve(n):
    is_p = bytearray([1]) * (n + 1)
    is_p[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = bytearray(len(is_p[i * i :: i]))
    return is_p


def prime_factors(n, spf):
    out = []
    while n > 1:
        q = spf[n]
        out.append(q)
        while n % q == 0:
            n //= q
    return out


def smallest_prime_factor(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


failures = 0


def report(name, ok, detail):
    global failures
    print(f"{'PASS' if ok else 'FAIL'} {name}: {detail}")
    if not ok:
        failures += 1


# (A) least prime primitive roots
is_p = sieve(LIMIT)
spf = smallest_prime_factor(LIMIT)
primes = [i for i in range(2, LIMIT + 1) if is_p[i]]
worst_g, worst_p, total, count, ok = 0, 0, 0, 0, True
for p in primes:
    if p == 2:
        continue
    qs = [(p - 1) // r for r in prime_factors(p - 1, spf)]
    g = None
    for ell in primes:
        if ell >= p:
            break
        if all(pow(ell, e, p) != 1 for e in qs):
            g = ell
            break
    if g is None:
        ok = False
        break
    total += g
    count += 1
    if g > worst_g:
        worst_g, worst_p = g, p
report("A", ok, f"{count} primes 3..{LIMIT}, max G(p) = {worst_g} at p = {worst_p}, sum G(p) = {total}")

# (B) the character identity
ok = True
for p in primes:
    if p > 200:
        break
    N = p - 1
    g = next(a for a in range(1, p) if all(pow(a, N // r, p) != 1 for r in prime_factors(N, spf)) or N == 1)
    log = {pow(g, k, p): k for k in range(N)}
    zeta = cmath.exp(2j * math.pi / N)
    divs = [d for d in range(1, N + 1) if N % d == 0]
    mu = {}
    for d in divs:
        fs = prime_factors(d, spf)
        prod = 1
        for f in fs:
            prod *= f
        mu[d] = 0 if prod != d else (-1) ** len(fs)
    for n in range(3 * p):
        r = n % p
        lhs = 1 if (r != 0 and math.gcd(log[r], N) == 1) else 0
        rhs = 0j
        for d in divs:
            inner = 0j
            for m in range(d):
                j = m * (N // d)
                inner += 0 if r == 0 else zeta ** (log[r] * j % N)
            rhs += mu[d] / d * inner
        if abs(rhs - lhs) > 1e-8:
            ok = False
report("B", ok, "indicator of primitive roots = sum over d | p-1 of mu(d)/d sum_{m<d} chi^{m(p-1)/d}, p <= 200")

# (C) psi(x/2)/2 - log x >= x/10 for x >= 10^4, checked on the cells [2m, 2m+2)
ok = True
psi = 0.0
worst = float("inf")
lam = [0.0] * (M_LIMIT + 1)
for q in primes:
    if q > M_LIMIT:
        break
    lq = math.log(q)
    k = q
    while k <= M_LIMIT:
        lam[k] = lq
        k *= q
for m in range(1, M_LIMIT + 1):
    psi += lam[m]
    if m >= 5000:
        margin = psi / 2 - ((2 * m + 2) / 10 + math.log(2 * m + 2))
        worst = min(worst, margin)
        if margin < 0:
            ok = False
report("C", ok, f"psi(m)/2 - (2m+2)/10 - log(2m+2) >= 0 for 5000 <= m <= {M_LIMIT}, least margin {worst:.3f}")

# (D) phi(N)/N >= 1/tau(N)
ok = True
for N in range(1, 10**6 + 1):
    fs = prime_factors(N, spf)
    phi, tau, n = N, 1, N
    for f in fs:
        phi = phi // f * (f - 1)
        e = 0
        while n % f == 0:
            n //= f
            e += 1
        tau *= e + 1
    if phi * tau < N:
        ok = False
        break
report("D", ok, "phi(N) tau(N) >= N for N <= 10^6")

# (E) exponent arithmetic: e = eta/(2000(8+eta)), sigma0 = 7/8+8e, beta = 1/8-8e
ok = True
for eta in [Fraction(1, 10**6), Fraction(1, 1000), Fraction(1, 7), Fraction(1), Fraction(5), Fraction(10**6)]:
    e = eta / (2000 * (8 + eta))
    beta = Fraction(1, 8) - 8 * e
    sigma0 = Fraction(7, 8) + 8 * e
    ok &= 0 < e < Fraction(1, 1000) and beta > 0 and (8 + eta) * beta >= 1 and sigma0 + beta == 1
    ok &= (8 + eta) * 8 * e == eta / 250
report("E", ok, "0 < e < 1/1000, beta > 0, (8+eta) beta = 1 + eta/8 - eta/250 >= 1")

# (F1) partial sums of sum chi_{-3}(n) Lambda(n) n^{-2} do not tend to 0
chi = lambda n: 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)
s, ok, X = 0.0, True, 10**6
for n in range(2, X + 1):
    if lam[n]:
        s += chi(n) * lam[n] / n**2
report("F1", abs(s) > 0.1, f"sum_(n <= 10^6) chi_-3(n) Lambda(n) / n^2 = {s:.6f} (Carella [Car15, (16)] asserts O(1/x))")

# (F2) for u not a primitive root, sum_{0<m<p} e(-um/p) sum_{(n,p-1)=1} e(m tau^n / p) = -phi(p-1):
# every u in [0, p) for p = 101, 1009, and u = 1 for p = 10007
ok = True
for p in [101, 1009, 10007]:
    N = p - 1
    g = next(a for a in range(2, p) if all(pow(a, N // r, p) != 1 for r in prime_factors(N, spf)))
    roots = [pow(g, n, p) for n in range(1, N + 1) if math.gcd(n, N) == 1]
    is_root = [False] * p
    for r in roots:
        is_root[r] = True
    w = [cmath.exp(2j * math.pi * k / p) for k in range(p)]
    S = [sum(w[m * r % p] for r in roots) for m in range(p)]
    phi = len(roots)
    us = range(p) if p < 5000 else [1]
    worst = 0.0
    for u in us:
        total_val = sum(w[(-u * m) % p] * S[m] for m in range(1, p))
        expected = p - phi if is_root[u] else -phi
        worst = max(worst, abs(total_val - expected))
    ok &= worst < 1e-6 * p
    print(f"     p = {p}: {len(us)} values of u checked, max error {worst:.2e}, -phi(p-1) = {-phi}")
report("F2", ok, "the double sum of [Car18, (7.2)] equals -phi(p-1) whenever u is not a primitive root")

print(f"{'ALL PASS' if failures == 0 else str(failures) + ' FAILED'}")
sys.exit(1 if failures else 0)
