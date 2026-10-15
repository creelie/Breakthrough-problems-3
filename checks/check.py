#!/usr/bin/env python3
"""Numerical checks for "The Pólya–Vinogradov inequality with log log q".

(A) Lemma 2.1 (Chebyshev's bounds) for x, N <= 10^6;
(B) Lemma 2.2: the Selberg weights satisfy lambda_1 = 1, |lambda_d| <= 1 and Q = 1/S, in exact
    rationals, and the sieve bound holds for a_n = n(n + 2);
(C) Lemmas 3.3, 3.4 and 3.6: the logarithm bound, Borel-Caratheodory for random polynomials,
    and the two elementary inequalities on grids;
(D) the exponent arithmetic of Section 3 and of the proof of Theorem 1.3(ii), in exact rationals;
(E) Corollary 3.8: the identity for T(x + h) - T(x), the inequalities used for h = x^(47/50),
    and max |sum_{p<=x} xi(p) log p| / (x^(19/20) log(k+2)) for quadratic xi, x <= 10^6;
(F) Lemmas 4.2 and 4.3 (spacing of the multiples of alpha, bilinear bounds) on random data;
(G) Lemma 4.4 for characters and random completely multiplicative f;
(H) Lemma 4.5: the prime pair bound for X <= 10^5 and even 2 <= h <= 100, the sieve remainders,
    and the fourth moment of G(h) for X <= 10^5;
(I) the numerical constants and the parameters I, J in the proof of Theorem 4.1;
(J) Lemma 5.1: |tau|^2 = q and the bound for the quadratic characters modulo primes q <= 3000,
    max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000, and the
    bound |r(theta)| < 3 on a grid;
(K) Lemma 5.2 for Y <= 10^6, the sum of m^(-19/20) in Lemma 5.3, and the parameter
    inequalities in the proof of Proposition 5.4;
(L) Lemmas 6.2 and 6.3: the block counts against the sieve bound for primes 101 <= q <= 401, the
    claim N_j <= 393 * 2^j/(j+1) where it can be counted, and the inequalities of the proof;
(M) Theorem 1.3: L'/L(1, chi) for every nonprincipal chi modulo the primes q <= 300, from the
    Hurwitz zeta function at s = 1, and the Euler-Kronecker constants
    gamma_q = gamma + sum_{chi != 1} L'/L(1, chi), against reference values from mpmath.
Prints one line per check and exits with status 1 if any check fails.
"""
import cmath
import math
import sys
from fractions import Fraction

LIMIT = 10**6


def sieve(n):
    is_p = bytearray([1]) * (n + 1)
    is_p[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = bytearray(len(is_p[i * i :: i]))
    return is_p


def smallest_prime_factor(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def prime_factors(n, spf):
    out = []
    while n > 1:
        p = spf[n]
        out.append(p)
        while n % p == 0:
            n //= p
    return out


def legendre(n, q):
    r = pow(n % q, (q - 1) // 2, q)
    return 0 if r == 0 else (1 if r == 1 else -1)


state = 12345


def rnd():
    global state
    state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
    return (state >> 11) / 2**53


failures = 0


def report(name, ok, detail):
    global failures
    print(f"{'PASS' if ok else 'FAIL'} {name}: {detail}", flush=True)
    if not ok:
        failures += 1


is_p = sieve(4 * LIMIT)
spf = smallest_prime_factor(LIMIT)
primes = [i for i in range(2, LIMIT + 1) if is_p[i]]

# (A) Lemma 2.1
ok, theta, psi, sl, sr = True, 0.0, 0.0, 0.0, 0.0
w1 = w2 = w3 = 0.0
for n in range(2, LIMIT + 1):
    p = spf[n]
    m = n
    while m % p == 0:
        m //= p
    if m == 1:                       # n is a power of p
        psi += math.log(p)
        if n == p:
            theta += math.log(p)
            sl += math.log(p) / p
            sr += 1 / p
    w1 = max(w1, theta / (n * math.log(4)))
    w2 = max(w2, (psi - theta) / (2 * math.sqrt(n) * math.log(n)))
    w3 = max(w3, psi / (4 * n))
    ok &= sl <= math.log(n) + math.log(4) and sr <= math.log(math.log(n)) + 10
ok &= w1 <= 1 and w2 <= 1 and w3 <= 1
report("A", ok, f"theta(x) <= x log 4 (max ratio {w1:.4f}), psi - theta <= 2 sqrt(x) log x ({w2:.4f}), "
       f"psi(x) <= 4x ({w3:.4f}), (iii) and (iv) for x, N <= 10^6")


# (B) Lemma 2.2: Selberg's weights in exact rationals
def selberg(ps, nu_p, y):
    divs = [1]
    for p in ps:
        divs += [d * p for d in divs]
    D = sorted(d for d in divs if d * d <= y)
    fac = {d: [p for p in ps if d % p == 0] for d in divs}

    def nu(d):
        r = Fraction(1)
        for p in fac[d]:
            r *= nu_p(p)
        return r

    def g(d):
        r = Fraction(1)
        for p in fac[d]:
            r *= nu_p(p) / (1 - nu_p(p))
        return r

    S = sum(g(l) for l in D)
    lam = {}
    for d in D:
        tot = sum(g(e) for e in D if math.gcd(e, d) == 1 and (d * e) ** 2 <= y)
        lam[d] = (-1) ** len(fac[d]) * g(d) / (nu(d) * S) * tot
    return D, lam, S, nu


ok, cases = True, 0
for ps, nu_p in [([2, 3, 5, 7, 11, 13], lambda p: Fraction(1, p)),
                 ([3, 5, 7, 11, 13, 17], lambda p: Fraction(2, p)),
                 ([2, 5, 7, 13, 19], lambda p: Fraction(1, p + 1))]:
    for y in [1, 4, 30, 200, 3000, 10**5]:
        D, lam, S, nu = selberg(ps, nu_p, y)
        Q = sum(lam[a] * lam[b] * nu(a * b // math.gcd(a, b)) for a in D for b in D)
        ok &= lam[1] == 1 and all(abs(v) <= 1 for v in lam.values()) and Q * S == 1
        cases += 1
for X in [100, 1000, 10**4]:          # the bound for a_n = n(n+2), 0 <= n < X, nu(p) = 2/p
    for z, y in [(5, 30), (7, 60), (11, 150), (13, 200)]:
        ps = [p for p in [3, 5, 7, 11, 13] if p <= z]
        D, lam, S, nu = selberg(ps, lambda p: Fraction(2, p), y)
        P = math.prod(ps)
        cnt = sum(1 for n in range(X) if math.gcd(n * (n + 2), P) == 1)
        err = 0
        for d in range(1, y + 1):
            if P % d == 0:
                k = sum(1 for p in ps if d % p == 0)
                Rd = sum(1 for n in range(X) if n * (n + 2) % d == 0) - Fraction(2 ** k, d) * X
                err += 3 ** k * abs(Rd)
        ok &= cnt <= X / S + err
        cases += 1
report("B", ok, f"lambda_1 = 1, |lambda_d| <= 1, Q = 1/S and the sieve bound in {cases} cases, exact")

# (C) Lemmas 3.3, 3.4 and 3.6
ok, worst = True, 0.0
for i in range(1, 401):
    for k in range(0, 360):
        w = (i / 800) * cmath.exp(1j * math.pi * k / 180)
        worst = max(worst, abs(cmath.log(1 - w)) / abs(w))
ok &= worst <= 1.5
A0 = 1.5 * sum(p ** -1.5 for p in primes)
for _ in range(400):
    deg = 1 + int(6 * rnd())
    co = [complex(2 * rnd() - 1, 2 * rnd() - 1) for _ in range(deg + 1)]
    c = complex(2 * rnd() - 1, 2 * rnd() - 1)
    R = 0.2 + 2 * rnd()
    r = R * (0.05 + 0.9 * rnd())
    h = lambda z: sum(a * z ** j for j, a in enumerate(co))
    hc = h(c)
    A = max((h(c + R * cmath.exp(2j * math.pi * k / 720)) - hc).real for k in range(720))
    lhs = max(abs(h(c + r * cmath.exp(2j * math.pi * k / 360)) - hc) for k in range(360))
    ok &= lhs <= 2 * r / (R - r) * A * (1 + 1e-6) + 1e-12
for qq in [1, 2, 3, 10, 1000, 10**9]:
    for k in range(0, 4001):
        t = 10 ** (k / 500) - 1
        ok &= math.log(2 * qq * (3 + t) ** 2) <= 10 * math.log(qq + 2) * math.sqrt(1 + t)
        for sig in [0.5, 0.7, 1.0, 2.0, 5.0]:
            s = complex(sig, t)
            ok &= abs(s * (s + 1)) >= (1 + t) ** 2 / 8
report("C", ok, f"|log(1-w)| <= 1.5|w| on |w| <= 1/2 (max ratio {worst:.4f}), A_0 = {A0:.5f}; "
       "Borel-Caratheodory for 400 random polynomials; Lemma 3.6 on grids")

# (D) exponents
F = Fraction
delta, a = F(1, 2000), F(7, 8) - F(1, 1000)
sigma0 = a + 8 * delta
ok = 0 < delta < F(1, 1000) and F(1, 2) <= a <= 1 and a + 2 * delta == F(7, 8)
ok &= sigma0 == F(7, 8) + F(3, 1000) and 1 + sigma0 - F(47, 50) < F(19, 20)
ok &= 17 * (sigma0 - 1) < -2 and 2 ** float(1 + sigma0) <= 4
report("D", ok, f"sigma_0 = {sigma0} = 7/8 + 3/1000, 1 + sigma_0 - 47/50 = {1 + sigma0 - F(47, 50)} < 19/20, "
       f"17(sigma_0 - 1) = {17 * (sigma0 - 1)} < -2")

# (E) Corollary 3.8
ok, cases = True, 0
for q in [3, 5, 101]:
    lam = [0.0] * 3001
    for n in range(2, 3001):
        p = spf[n]
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            lam[n] = legendre(n, q) * math.log(p)
    T = lambda y: sum(lam[n] * (y - n) for n in range(1, math.floor(y) + 1))
    for _ in range(40):
        x = 1 + 1400 * rnd()
        h = x * rnd()
        fx, fxh = math.floor(x), math.floor(x + h)
        lhs = T(x + h) - T(x)
        rhs = h * sum(lam[1:fx + 1]) + sum(lam[n] * (x + h - n) for n in range(fx + 1, fxh + 1))
        ok &= abs(lhs - rhs) <= 1e-7 * (1 + abs(lhs)) and fxh - fx <= h + 1
        cases += 1
for k in range(0, 6001):
    x = 10 ** (k / 100)
    ok &= math.log(2 * x) <= 1 + 100 * x ** 0.01 and 2 * math.sqrt(x) * math.log(x) <= 200 * x ** 0.95
worst = 0.0
for q in [3, 5, 7, 11, 13, 101, 997]:
    run = 0.0
    for p in primes:
        run += legendre(p, q) * math.log(p)
        worst = max(worst, abs(run) / (p ** 0.95 * math.log(q + 2)))
report("E", ok, f"T(x+h) - T(x) identity in {cases} cases, log(2x) <= 1 + 100 x^(1/100), "
       f"2 sqrt(x) log x <= 200 x^(19/20); max |sum xi(p) log p| / (x^(19/20) log(k+2)) = {worst:.4f}")


def dist(x):
    return abs(x - round(x))


def wM(M, th):
    d = dist(th)
    return M if d < 1 / M else 1 / d


# (F) Lemmas 4.2 and 4.3
ok, cases = True, 0
for _ in range(3000):
    r = 2 + int(400 * rnd())
    a = int(r * rnd())
    while math.gcd(a, r) != 1:
        a = (a + 1) % r
    alpha = a / r + (2 * rnd() - 1) / r ** 2 + int(20 * rnd()) - 10
    for k in range(1, r // 2 + 1):                                   # (i)
        ok &= dist(k * alpha) >= 1 / (2 * r) - 1e-12
    H = int(1000 * rnd())
    ds = [dist(h * alpha) for h in range(1, H + 1)]
    for _ in range(3):                                               # (ii)
        t = 0.5 * rnd()
        ok &= sum(1 for d in ds if d < t) <= (4 * H / r + 1) * (4 * r * t + 1)
    M = 0.5 + 1000 * rnd()
    K = max(0, math.ceil(math.log2(M)))
    ws = [M if d < 1 / M else 1 / d for d in ds]
    ok &= sum(ws) <= (4 * H / r + 1) * (3 * M + 4 * r + 8 * r * K)    # (iii)
    ok &= sum(w * w for w in ws) <= (4 * H / r + 1) * (20 * r * M + 3 * M * M)
    cases += 1
for _ in range(2000):                                                # Lemma 4.3 (i)
    th = 2 * rnd() - 1
    U = 0.5 + 300 * rnd()
    A = int(1000 * rnd())
    B = A + int(U * rnd())
    S = sum(cmath.exp(2j * math.pi * x * th) for x in range(A + 1, B + 1))
    ok &= abs(S) <= wM(U, th) * (1 + 1e-9)
for _ in range(300):                                                 # Lemma 4.3 (ii), (iii)
    alpha = rnd()
    U = 1 + 50 * rnd()
    A = int(100 * rnd())
    B = A + int(U)
    N = int(2000 * rnd()) + 1
    V = sorted(set(1 + int(60 * rnd()) for _ in range(1 + int(20 * rnd()))))
    b = {v: cmath.exp(2j * math.pi * rnd()) * rnd() for v in V}
    lhs = sum(abs(sum(b[v] * cmath.exp(2j * math.pi * u * v * alpha) for v in V if u * v <= N)) ** 2
              for u in range(A + 1, B + 1))
    rhs = sum(abs(b[v]) * abs(b[w]) * wM(U, (v - w) * alpha) for v in V for w in V)
    ok &= lhs <= rhs * (1 + 1e-9) + 1e-9
    Hh = int(80 * rnd())
    Mm = 0.5 + 100 * rnd()
    lhs = sum(wM(Mm, (m - m2) * alpha) for m in range(1, Hh + 1) for m2 in range(1, Hh + 1))
    ok &= lhs <= Hh * (Mm + 2 * sum(wM(Mm, h * alpha) for h in range(1, Hh + 1))) * (1 + 1e-12)
report("F", ok, f"Lemma 4.2 (i)-(iii) for {cases} random (alpha, a/r), Lemma 4.3 (i) at 2000 and (ii), (iii) "
       "at 300 random cases")

# (G) Lemma 4.4
zeta32 = 2.612375348685488
C5 = 1 + 4 * zeta32
ok, worst = True, 0.0
for trial in range(60):
    N = 2 + int(2998 * rnd())
    alpha = rnd()
    fp = {}
    if trial % 3 == 0:
        q = [3, 5, 7, 11, 101, 997][trial // 3 % 6]
        f = [0j] + [complex(legendre(n, q)) for n in range(1, N + 1)]
    else:
        f = [0j] * (N + 1)
        f[1] = 1
        for n in range(2, N + 1):
            p = spf[n]
            if p not in fp:
                fp[p] = cmath.exp(2j * math.pi * rnd()) * (rnd() if trial % 3 == 2 else 1)
            f[n] = fp[p] * f[n // p]
    S = sum(f[n] * cmath.exp(2j * math.pi * n * alpha) for n in range(1, N + 1))
    T = 0j
    for p in range(2, N + 1):
        if spf[p] == p:
            T += math.log(p) * f[p] * sum(f[m] * cmath.exp(2j * math.pi * p * m * alpha)
                                          for m in range(1, N // p + 1))
    err = abs(S * math.log(N) - T) / N
    worst = max(worst, err)
    ok &= err <= C5
report("G", ok, f"Lemma 4.4 for 60 completely multiplicative f, N <= 3000: max error / N = {worst:.4f} "
       f"<= C_5 = {C5:.4f}")

# (H) Lemma 4.5
XO = 10**5


def Gfun(h):
    g = 1.0
    for p in prime_factors(h, spf):
        g *= p / (p - 1)
    return g


ok, worst = True, 0.0
for h in range(2, 101, 2):
    g2 = Gfun(h) ** 2
    bound = lambda X: 400 * g2 * X / math.log(X) ** 2 + 3 * X ** 0.6
    # the count for X changes only at X = n + 1 for a pair (n, n + h), and the bound increases for
    # X >= 8, so it suffices to check every X <= 8 and every jump
    cnt = 0
    for X in range(2, XO + 1):
        n = X - 1
        jump = is_p[n] and is_p[n + h]
        if jump:
            cnt += 1
        if jump or X <= 8:
            ok &= cnt <= bound(X)
            worst = max(worst, cnt / bound(X))
for X in [1, 2, 7, 100, 1001, 2000]:
    for h in [2, 4, 6, 30, 98]:
        for d in [1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 3 * 5 * 7 * 11]:
            if math.gcd(d, h) != 1:
                continue
            k = sum(1 for p in [3, 5, 7, 11, 13] if d % p == 0)
            c = sum(1 for n in range(X) if (n * (n + h)) % d == 0)
            ok &= abs(c - 2 ** k * X / d) <= 2 ** k and 6 ** k <= d * d
for X in range(2, 10**5):                       # T = floor(X^(1/20)): (T+1)^20 > X
    T = int(round(X ** 0.05))
    while T ** 20 > X:
        T -= 1
    while (T + 1) ** 20 <= X:
        T += 1
    ok &= (T + 1) ** 20 > X
for m in range(1, 10**5):                       # tau(m) <= 2^Omega(m)
    n, tau, Om = m, 1, 0
    while n > 1:
        p, e = spf[n], 0
        while n % p == 0:
            n //= p
            e += 1
        tau *= e + 1
        Om += e
    ok &= tau <= 2 ** Om
acc, worstG = 0.0, 0.0
for h in range(1, XO + 1):
    acc += Gfun(h) ** 4
    worstG = max(worstG, acc / h)
ok &= worstG <= math.exp(30) and math.pi ** 2 / 6 - 1 <= 1
ok &= all((t + 1) ** 5 <= (t + 31) * t ** 4 for t in range(1, 10**5))
report("H", ok, f"prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, even 2 <= h <= 100 "
       f"(max ratio {worst:.4f}); |R_d| <= 2^omega(d); tau(m) <= 2^Omega(m); "
       f"max_X X^-1 sum G(h)^4 = {worstG:.3f} <= e^30")

# (I) constants and parameters in the proof of Theorem 4.1
ok = 64 * math.log(2) < 45
for ell in range(64, 10**4 + 1):
    I = ell.bit_length()                 # floor(log2 ell) + 1
    J = ell + 1 - 4 * I
    ok &= 16 ** I > ell ** 4 and 1 <= J <= ell and 4 * I <= ell and 2 ** I <= 2 * ell
    ok &= 2 ** J * 16 ** I == 2 ** (ell + 1)
    ok &= J * J * 2 ** J * ell ** 4 <= (ell + 1) ** 2 * 2 ** (ell + 1) and (ell + 1) ** 2 <= ell ** 4
ok &= 1 / math.log(2) <= 2                # ell <= log2 N <= 2 log N
ok &= Fraction(7, 4) / Fraction(1, 4) ** 3 == 112   # sum (j+1)^2 x^j = (1+x)/(1-x)^3 at x = 3/4
ok &= all((1 + 2 * j) * 8 ** j <= 2 * (j + 1) ** 2 * 9 ** j for j in range(2000))
ok &= all(sum(2 ** (j / 2) for j in range(J)) <= 3 * 2 ** (J / 2) for J in range(1, 200))
ok &= 3 * math.sqrt(14) <= 12 and math.sqrt(24) <= 5 and 8 * 112 + 12 == 908
ok &= 6 * 225 == 1350 <= 37 ** 2 and 15 + 37 == 52
coeffs = [320 * 15 ** 3, 48 * 15 ** 4, 80 * 15 ** 3, 180 * 15 ** 3]
ok &= all(c <= 40 ** 4 for c in coeffs) and 2 ** 0.25 <= 2
ok &= 2 ** 0.3 <= 2 and 2 + 16 + 32 * 2 * 15 ** 3 == 216018
ok &= all(math.log(x) <= 15 * x ** (1 / 15) for x in [1 + 10 ** (k / 10) for k in range(0, 3000)])
ok &= all(math.log(x) <= 4 * x ** 0.25 for x in [1 + 10 ** (k / 10) for k in range(0, 3000)])
ok &= all(N * math.log(N) - math.lgamma(N + 1) <= N for N in range(1, 10**4))
pl = sum(math.log(p) / (p * (p - 1)) for p in primes)
ok &= pl <= 2 * sum(math.log(p) / p ** 2 for p in primes) <= 2 * zeta32
Kb = 80 * math.sqrt(800 * math.exp(15)) + 52
C1 = 45 + C5 + 908 + 216018 * Kb + 60 + 2 * Kb
report("I", ok, f"constants of Theorem 4.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; "
       f"K_b = {Kb:.4e}, C_1 = {C1:.4e}")


# (J) Lemma 5.1
def quad_table(q):
    tab = [-1] * q
    tab[0] = 0
    for a in range(1, q):
        tab[a * a % q] = 1
    return tab


ok, worst_tau, nq, worst_ratio = True, 0.0, 0, 0.0
for q in range(3, 20001):
    if not is_p[q]:
        continue
    tab = quad_table(q)
    run, m = 0, 0
    for n in range(1, q):
        run += tab[n]
        m = max(m, abs(run))
    if q <= 3000:
        tau = sum(tab[a] * cmath.exp(2j * math.pi * a / q) for a in range(1, q))
        worst_tau = max(worst_tau, abs(abs(tau) ** 2 - q) / q)
        b0 = sum(1 / k for k in range(1, q // 2 + 1))
        ok &= m <= math.sqrt(q) * (b0 + 6)
        nq += 1
    if q >= 1000:
        worst_ratio = max(worst_ratio, m / (math.sqrt(q) * math.log(math.log(q))))
worst = 0.0
for k in range(1, 500001):
    for th in (k / 10**6, -k / 10**6):
        r = 1 / (1 - cmath.exp(-2j * math.pi * th)) - 1 / (2j * math.pi * th)
        worst = max(worst, abs(r))
ok &= worst_tau < 1e-9 and worst_ratio < 2 and worst < 3
report("J", ok, f"|tau|^2 = q (max rel. error {worst_tau:.1e}) and max|S| <= sqrt(q)(B+6) for {nq} primes; "
       f"max ratio for 1000 <= q <= 20000: {worst_ratio:.4f}; max |r(theta)| = {worst:.6f} < 3")

# (K) Lemma 5.2, Lemma 5.3, Proposition 5.4
ok, prod, worstS = True, 1.0, 0.0
for Y in range(2, LIMIT + 1):
    if is_p[Y]:
        prod /= 1 - 1 / Y
    worstS = max(worstS, prod / (math.exp(11) * math.log(Y)))
ok &= worstS <= 1
s19 = 0.0
for m in range(1, 10**6 + 1):
    s19 += m ** -0.95
    if m % 997 == 0 or m < 100:
        ok &= s19 <= 20 * m ** 0.05
for L in [200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9]:
    M = math.ceil(L)
    lM = math.log(M)
    ok &= (L / 16) ** 4 / 24 > L + 1 >= M and 16 * lM < L       # e^(L/16) > M, so R < q
    ok &= M ** 16 >= 2 and lM >= 1 and M <= 2 * L
    rho = L ** 2 / M ** 4
    ok &= rho * (1 + L) <= 2 / M <= 1
    logqR = L + 16 * lM + math.log1p(2 * math.exp(-L - 16 * lM))  # log(q R + 2)
    ok &= logqR <= 18 * M and 2 + 2 * math.pi * M ** 16 <= 8 * M ** 16
    k = logqR * (2 / M ** 16 + 2 * math.pi) / (M ** 3 * 700 * lM)  # R log(qR+2)(2+2 pi R)/(Y^(1/20) log Y)
    ok &= k * (1 + L) <= 288 / (700 * M) <= 1
    ok &= 700 <= 700 * lM <= 1400 * math.log(L)
s1 = 0.0
for t in range(2, 10**6 + 1):
    s1 += 1 / (t * math.log(t))
    if t in (2, 3, 10, 100, 10**3, 10**4, 10**5, 10**6):
        ok &= s1 <= 3 + math.log(math.log(t)) if t >= 3 else s1 <= 3
report("K", ok, f"prod_(p<=Y) (1-1/p)^-1 <= e^11 log Y for Y <= 10^6 (max ratio {worstS:.2e}); "
       "sum m^(-19/20) <= 20 M^(1/20); Proposition 5.4 at 8 values of log q")

# (L) Lemmas 6.2 and 6.3
XL = 4 * LIMIT


def is_prime_power(n):
    if is_p[n]:
        return True
    p = spf[n] if n <= LIMIT else next(p for p in primes if n % p == 0)
    while n % p == 0:
        n //= p
    return n == 1


ok, cases, worstB, worstN = True, 0, 0.0, 0.0
for q in [p for p in primes if 101 <= p <= 401]:
    j = 0
    while 2 ** (j + 1) * q <= XL:
        M = 2 ** j
        cnt = sum(1 for m in range(M, 2 * M) if is_prime_power(1 + m * q))
        worstN = max(worstN, cnt / (393 * M / (j + 1)))
        ok &= cnt <= 393 * M / (j + 1)
        for z in sorted({2, 3, 5, 10, 30, math.isqrt(q), q - 1}):
            bnd = 2 * M / math.log(z) + z * (1 + math.log(z)) ** 2 + z
            worstB = max(worstB, cnt / bnd)
            ok &= cnt <= bnd
            cases += 1
        j += 1
for k in range(0, 200001):
    u = 1 + k / 1000
    ok &= (2 + u) ** 2 * (32 * u + 1) <= 297 * u ** 3 and u ** 3 <= 2 ** (3 * u)
    ok &= (1 + u * math.log(2)) ** 2 + 1 <= (2 + u) ** 2
ok &= all(64 * (j + 1) <= 96 * j * math.log(2) for j in range(32, 10**5))
ok &= 50 * math.log(2) <= 35 and math.log(25) <= 4 and math.log(math.log(3)) > 1 / 11
ok &= 40 <= 440 * math.log(math.log(3)) and 393 == 96 + 297
for q in primes[1:]:
    J = math.floor(16 * math.log2(q)) + 1
    ok &= J <= 25 * math.log(q) and 2 ** J > q ** 16 and 2 ** J <= 2 * q ** 16
report("L", ok, f"block counts <= sieve bound in {cases} cases (max ratio {worstB:.4f}); N_j <= 393 2^j/(j+1) "
       f"(max ratio {worstN:.4f}); the inequalities of Lemma 6.3 on grids and for primes q <= 10^6")

# (M) Theorem 1.3: L'/L(1, chi) = -log q + sum chi(a) gamma_1(a/q) / sum chi(a) psi(a/q)
B2 = [Fraction(1, 6), Fraction(-1, 30), Fraction(1, 42), Fraction(-1, 30), Fraction(5, 66),
      Fraction(-691, 2730), Fraction(7, 6), Fraction(-3617, 510)]
HARM = [sum(Fraction(1, i) for i in range(1, n + 1)) for n in range(20)]
EM_N = 30


def digamma(a):
    x = a + EM_N
    s = math.log(x) - 1 / (2 * x) - sum(float(B2[j]) / ((2 * j + 2) * x ** (2 * j + 2)) for j in range(8))
    return s - sum(1 / (a + k) for k in range(EM_N))


def stieltjes1(a):
    # gamma_1(a) = lim_M (sum_{k<=M} log(k+a)/(k+a) - log^2(M+a)/2), by Euler-Maclaurin at x = a + N
    x = a + EM_N
    lx = math.log(x)
    s = sum(math.log(a + k) / (a + k) for k in range(EM_N)) - lx * lx / 2 + lx / (2 * x)
    s += sum(float(B2[j]) * (lx - float(HARM[2 * j + 1])) / ((2 * j + 2) * x ** (2 * j + 2)) for j in range(8))
    return s


EULER = 0.5772156649015329
ok = abs(digamma(1) + EULER) < 1e-13 and abs(stieltjes1(1) + 0.0728158454836767) < 1e-13
ok &= abs(digamma(0.5) + EULER + 2 * math.log(2)) < 1e-13


def primitive_root(q):
    fs = prime_factors(q - 1, spf)
    return next(g for g in range(2, q) if all(pow(g, (q - 1) // f, q) != 1 for f in fs))


def ek(q):
    g = primitive_root(q)
    pw = [pow(g, k, q) for k in range(q - 1)]
    ps = [digamma(pw[k] / q) for k in range(q - 1)]
    g1 = [stieltjes1(pw[k] / q) for k in range(q - 1)]
    roots = [cmath.exp(2j * math.pi * m / (q - 1)) for m in range(q - 1)]
    tot, mx = 0j, 0.0
    for j in range(1, q - 1):
        num = sum(roots[j * k % (q - 1)] * g1[k] for k in range(q - 1))
        den = sum(roots[j * k % (q - 1)] * ps[k] for k in range(q - 1))
        r = -math.log(q) + num / den
        tot += r
        mx = max(mx, abs(r))
    return EULER + tot, mx


# gamma_q from mpmath at 90 digits: euler + sum over chi != 1 of L'/L(1, chi), the logarithmic
# derivative taken from the Hurwitz zeta function and its derivative at s = 1 + 10^-25
REF = {3: 0.945497280871680703, 5: 1.72062421251340476, 7: 2.08759407471733013,
       11: 2.41542590428326783, 13: 2.6107577374176502, 19: 4.79040941571428333,
       101: 5.29701289150966972, 199: 6.47366513609320739, 293: 3.38438152121953979}
lo, hi, mxr, vals = 1e9, -1e9, 0.0, {}
for q in [p for p in primes if 3 <= p <= 300]:
    gq, mx = ek(q)
    vals[q] = gq.real
    ok &= abs(gq.imag) < 1e-9
    lo, hi = min(lo, gq.real / math.log(q)), max(hi, gq.real / math.log(q))
    mxr = max(mxr, mx / math.log(math.log(q)))
worstR = max(abs(vals[q] - v) for q, v in REF.items()) if REF else 0.0
ok &= worstR < 1e-9
report("M", ok, f"gamma_q for primes 3 <= q <= 300 is real with {lo:.4f} <= gamma_q/log q <= {hi:.4f}; "
       f"max |L'/L(1,chi)|/log log q = {mxr:.4f}; gamma_3 = {vals[3]:.12f}, gamma_19 = {vals[19]:.12f}; "
       f"{len(REF)} values agree with mpmath to {worstR:.1e}")

print(f"{'ALL PASS' if failures == 0 else str(failures) + ' FAILED'}")
sys.exit(1 if failures else 0)
