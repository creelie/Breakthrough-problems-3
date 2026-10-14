#!/usr/bin/env python3
"""Numerical checks for "The Pólya–Vinogradov inequality with log log q".

(A) least prime primitive root G(p) < p for every prime 3 <= p <= LIMIT;
(B) the character identity of Lemma 3.1 for every prime p <= 200 and 0 <= n < 3p;
(C) psi(m)/2 >= (2m+2)/10 + log(2m+2) for 5000 <= m <= M_LIMIT (Lemma 3.3);
(D) phi(N)/N >= 1/tau(N) for 1 <= N <= 10^6 (Lemma 3.2);
(E) the exponent arithmetic of Section 4, in exact rationals;
(F) the two computations of Remark 1.11 on Carella's estimates;
(G) the unsmoothing identity of Lemma 5.2, in exact rationals;
(H) the kernel and size bounds in the proof of Proposition 5.3, at random points;
(I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6, in exact rationals;
(J) |tau|^2 = q and Lemma 7.1 for the quadratic characters modulo primes q <= 3000, and
    max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
(K) the bound |r(theta)| < 3 in the proof of Lemma 7.1 on a grid;
(L) the parameter inequalities in the proof of Proposition 7.4;
(M) Lemmas 6.2 and 6.3 (spacing of the multiples of alpha, the bilinear bounds) on random data;
(N) Lemma 6.4 for characters and random completely multiplicative f;
(O) Lemma 6.5: the prime pair bound for X <= 10^5 and even 0 < |h| <= 100, the sieve
    remainders |R_d| <= tau(d), and the fourth moment of G(h) for X <= 10^5;
(P) the numerical constants and the parameters I, J in the proof of Theorem 6.1.
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

# (G) T(x+h) - T(x) - h S(x) = sum_{x<n<=x+h} chi(n)(x+h-n), of absolute value <= h(h+1),
# where T(y) = sum_{n<=y} chi(n)(y-n) and S(x) = sum_{n<=x} chi(n)
def legendre(n, q):
    r = pow(n % q, (q - 1) // 2, q)
    return 0 if r == 0 else (1 if r == 1 else -1)

chars = [(lambda n: 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1), "chi_-4")]
for q in [3, 5, 7, 101, 997]:
    chars.append(((lambda q: lambda n: legendre(n, q))(q), f"(./{q})"))
ok, cases = True, 0
xs = [Fraction(1), Fraction(5, 2), Fraction(37, 3), Fraction(1000), Fraction(12345, 7)]
hs = [Fraction(1, 3), Fraction(1), Fraction(7, 2), Fraction(40), Fraction(333, 4)]
for chi, _ in chars:
    for x in xs:
        for h in hs:
            T = lambda y: sum(chi(n) * (y - n) for n in range(1, math.floor(y) + 1))
            S = sum(chi(n) for n in range(1, math.floor(x) + 1))
            lhs = T(x + h) - T(x) - h * S
            tail = sum(chi(n) * (x + h - n) for n in range(math.floor(x) + 1, math.floor(x + h) + 1))
            ok &= lhs == tail and abs(lhs) <= h * (h + 1)
            cases += 1
report("G", ok, f"(x+h)R(x+h) - xR(x) - h S(x) = tail, |tail| <= h(h+1): {cases} cases, exact")

# (H) for w = sigma+1+it: |(x+h)^w - x^w| <= min(|w| h (x+h)^sigma, 2 (x+h)^(sigma+1));
# for h = x^sigma0: (x+h)^sigma0 <= 2h, (3h)^(1-4e) <= 3h, (2(x+h))^(4e) <= 4 x^(4e)
state = 12345
def rnd():
    global state
    state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
    return (state >> 11) / 2**53
ok, worst = True, 0.0
for _ in range(200000):
    x = 1 + 10**6 * rnd()
    h = x * rnd()
    sigma = 0.5 + 1.5 * rnd()
    t = -100 + 200 * rnd()
    w = complex(sigma + 1, t)
    d = abs(cmath.exp(w * math.log(x + h)) - cmath.exp(w * math.log(x)))
    bound = min(abs(w) * h * (x + h) ** sigma, 2 * (x + h) ** (sigma + 1))
    worst = max(worst, d / bound)
    ok &= d <= bound * (1 + 1e-9)
    s0 = 0.5 + 0.5 * rnd()
    e = 0.125 * (1 - rnd())
    hh = x ** s0
    ok &= (x + hh) ** s0 <= 2 * hh * (1 + 1e-12) and (3 * hh) ** (1 - 4 * e) <= 3 * hh * (1 + 1e-12)
    ok &= (2 * (x + hh)) ** (4 * e) <= 4 * x ** (4 * e) * (1 + 1e-12)
report("H", ok, f"kernel and size bounds at 200000 random points, max ratio {worst:.6f}")

# (I) Theorems 1.4, 1.5 and Corollary 1.6: the parameters satisfy the hypotheses
ok = True
for dl in [Fraction(1, 10**6), Fraction(1, 1000), Fraction(1, 7), Fraction(1), Fraction(5), Fraction(1000)]:
    e1 = min(dl / 8, Fraction(1, 2000))
    a1 = Fraction(7, 8) - 2 * e1
    ok &= 0 < e1 < Fraction(1, 1000) and 8 * e1 <= dl and Fraction(1, 2) <= a1 <= 1 and a1 + 2 * e1 == Fraction(7, 8)
    ok &= a1 + 8 * e1 <= Fraction(7, 8) + dl
    d = min(dl, 1)
    e = min(d / 12, Fraction(1, 2000))
    eps = d / 8
    a = Fraction(7, 8) - 2 * e
    ok &= 0 < e < Fraction(1, 1000) and 0 < eps <= Fraction(1, 8) and Fraction(1, 2) <= a
    ok &= a + 8 * e <= 1 and a + 8 * e + 4 * eps <= Fraction(7, 8) + dl and a + 2 * e == Fraction(7, 8)
for eta, theta in [(Fraction(1, 1000), Fraction(7, 8) + Fraction(1, 10**6)), (Fraction(1), Fraction(9, 10)),
                   (Fraction(1000), Fraction(1)), (Fraction(1, 7), Fraction(15, 16))]:
    dc = (theta - Fraction(7, 8)) * eta / (1 + eta)
    ok &= dc > 0 and dc / eta + Fraction(7, 8) + dc == theta
report("I", ok, "parameters of Theorems 1.4, 1.5 and Corollary 1.6, exact rationals")

# (J) Gauss sums and Polya's bound for the quadratic characters (Lemma 7.1), and the ratio
# max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) (Theorem 1.7)
def quad_table(q):
    tab = [-1] * q
    tab[0] = 0
    for a in range(1, q):
        tab[a * a % q] = 1
    return tab

isp = sieve(20000)
ok, worst_tau, nq, worst_ratio = True, 0.0, 0, 0.0
for q in range(3, 20001):
    if not isp[q]:
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
ok &= worst_tau < 1e-9 and worst_ratio < 2
report("J", ok, f"|tau|^2 = q (max rel. error {worst_tau:.1e}) and max|S| <= sqrt(q)(B+6) for {nq} primes; "
       f"max ratio for 1000 <= q <= 20000: {worst_ratio:.4f}")

# (K) |1/(1 - e(-theta)) - 1/(2 pi i theta)| < 3 for 0 < |theta| <= 1/2
ok, worst = True, 0.0
for k in range(1, 500001):
    for th in (k / 10**6, -k / 10**6):
        r = 1 / (1 - cmath.exp(-2j * math.pi * th)) - 1 / (2j * math.pi * th)
        worst = max(worst, abs(r))
ok &= worst < 3
report("K", ok, f"|r(theta)| on 10^6 grid points of 0 < |theta| <= 1/2, max {worst:.6f}")

# (L) Proposition 7.4: M = ceil(L), R = M^16, Y = M^700
ok = True
for L in [200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9]:
    M = math.ceil(L)
    lM = math.log(M)
    ok &= (L / 16) ** 4 / 24 > L + 1 >= M and 16 * lM < L       # e^(L/16) > M, so R < q
    ok &= M ** 16 >= 2 and lM >= 1 and M <= 2 * L
    rho = L ** 2 / M ** 4
    ok &= rho * (1 + L) <= 2 / M <= 128
    logqR = L + 16 * lM + math.log1p(2 * math.exp(-L - 16 * lM))  # log(q R + 2)
    ok &= logqR <= 18 * M and 2 + 2 * math.pi * M ** 16 <= 8 * M ** 16
    # k = R log(qR+2) (2 + 2 pi R) / (Y^(1/20) log Y) with Y^(1/20) = M^35, written without overflow
    k = logqR * (2 / M ** 16 + 2 * math.pi) / (M ** 3 * 700 * lM)
    ok &= k * (1 + L) <= 288 / (700 * M) <= 1
    ok &= 700 * lM <= 1400 * math.log(L)
s1, ok1 = 0.0, True
for t in range(2, 10**6 + 1):
    s1 += 1 / (t * math.log(t))
    if t in (2, 3, 10, 100, 10**3, 10**4, 10**5, 10**6):
        ok1 &= s1 <= 3 + math.log(math.log(t)) if t >= 3 else s1 <= 3
ok &= ok1
report("L", ok, "parameter inequalities of Proposition 7.4 at 8 values of log q; "
       "sum_{2<=t<=H} 1/(t log t) <= 3 + log log H for H <= 10^6")

# (M) Lemma 6.2 (spacing) and Lemma 6.3 (bilinear bounds) on random data
def dist(x):
    return abs(x - round(x))

def wM(M, th):
    d = dist(th)
    return M if d < 1 / M else 1 / d

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
for _ in range(2000):                                                # Lemma 6.3 (i)
    th = 2 * rnd() - 1
    U = 0.5 + 300 * rnd()
    A = int(1000 * rnd())
    B = A + int(U * rnd())
    S = sum(cmath.exp(2j * math.pi * x * th) for x in range(A + 1, B + 1))
    ok &= abs(S) <= wM(U, th) * (1 + 1e-9)
for _ in range(300):                                                 # Lemma 6.3 (ii), (iii)
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
report("M", ok, f"Lemma 6.2 (i)-(iii) for {cases} random (alpha, a/r), Lemma 6.3 (i) at 2000 and (ii), (iii) at 300 random cases")

# (N) Lemma 6.4: |S log N - sum_p log p f(p) sum_{m<=N/p} f(m) e(pm alpha)| <= C5 N
zeta32 = 2.612375348685488
C5 = 1 + 4 * zeta32
ok, worst = True, 0.0
spf_small = smallest_prime_factor(3000)
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
            p = spf_small[n]
            if p not in fp:
                fp[p] = cmath.exp(2j * math.pi * rnd()) * (rnd() if trial % 3 == 2 else 1)
            f[n] = fp[p] * f[n // p]
    ev = [cmath.exp(2j * math.pi * n * alpha) for n in range(N + 1)]
    S = sum(f[n] * ev[n] for n in range(1, N + 1))
    T = 0j
    for p in range(2, N + 1):
        if spf_small[p] == p:
            T += math.log(p) * f[p] * sum(f[m] * cmath.exp(2j * math.pi * p * m * alpha) for m in range(1, N // p + 1))
    err = abs(S * math.log(N) - T) / N
    worst = max(worst, err)
    ok &= err <= C5
report("N", ok, f"Lemma 6.4 for 60 completely multiplicative f, N <= 3000: max error / N = {worst:.4f} <= C5 = {C5:.4f}")

# (O) Lemma 6.5
XO = 10**5
isp_o = sieve(XO + 200)

def Gfun(h):
    h = abs(h)
    g, p, n = 1.0, 2, h
    while p * p <= n:
        if n % p == 0:
            g *= p / (p - 1)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        g *= n / (n - 1)
    return g

ok, worst = True, 0.0
for h in list(range(2, 101, 2)) + list(range(-100, 0, 2)):
    g2 = Gfun(h) ** 2
    bound = lambda X: 400 * g2 * X / math.log(X) ** 2 + 3 * X ** 0.6
    # the count for X counts 0 <= n < X; it changes only at X = n + 1 for a pair (n, n + h), and the
    # bound increases for X >= 8, so it suffices to check every X <= 8 and every jump
    cnt = 0
    for X in range(2, XO + 1):
        n = X - 1
        jump = n + h >= 0 and isp_o[n] and isp_o[n + h]
        if jump:
            cnt += 1
        if jump or X <= 8:
            ok &= cnt <= bound(X)
            worst = max(worst, cnt / bound(X))
okR = True
for X in [1, 2, 7, 100, 1001, 2000]:
    for h in [2, 6, 30, 98, -4]:
        for d in [1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 3 * 5 * 7 * 11]:
            if math.gcd(d, h) != 1:
                continue
            tau = 2 ** sum(1 for p in [3, 5, 7, 11, 13] if d % p == 0)
            c = sum(1 for n in range(X) if (n * (n + h)) % d == 0)
            okR &= abs(c - tau * X / d) <= tau
# T = floor(sqrt(floor(X^(1/10)))) satisfies (T+1)^20 > X
okT = True
for X in list(range(2, 10**5)) + [10**k for k in range(6, 40)]:
    m = int(round(X ** 0.1)) + 2
    while m ** 10 > X:
        m -= 1
    T = math.isqrt(m)
    okT &= (T + 1) ** 20 > X
okG, acc, worstG = True, 0.0, 0.0
for h in range(1, XO + 1):
    g = 1.0
    for p in prime_factors(h, spf):
        g *= p / (p - 1)
    acc += g ** 4
    worstG = max(worstG, acc / h)
okG &= worstG <= math.exp(30)
okG &= all((t + 1) ** 5 <= (t + 31) * t ** 4 for t in range(1, 10**5))
okG &= math.pi ** 2 / 6 - 1 <= 1
ok &= okR and okT and okG
report("O", ok, f"prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, 0 < |h| <= 100 even "
       f"(max ratio {worst:.4f}); |R_d| <= tau(d); (T+1)^20 > X; max_X X^-1 sum G(h)^4 = {worstG:.3f} <= e^30")

# (P) constants and parameters in the proof of Theorem 6.1
ok = True
ok &= 64 * math.log(2) < 45
for ell in range(64, 10**4 + 1):
    I = ell.bit_length()                 # floor(log2 ell) + 1
    J = ell + 1 - 4 * I
    ok &= 16 ** I > ell ** 4 and 1 <= J <= ell and 4 * I <= ell and 2 ** I <= 2 * ell
    ok &= 2 ** J * 16 ** I == 2 ** (ell + 1)
    ok &= J * J * 2 ** J * ell ** 4 <= (ell + 1) ** 2 * 2 ** (ell + 1) and (ell + 1) ** 2 <= ell ** 4
ok &= math.log(2) >= 0.5                 # ell <= log2 N <= 2 log N
ok &= Fraction(7, 4) / Fraction(1, 4) ** 3 == 112   # sum (j+1)^2 x^j = (1+x)/(1-x)^3 at x = 3/4
tail = sum(Fraction((j + 1) ** 2 * 3 ** j, 4 ** j) for j in range(400))
ok &= 111.99 < float(tail) <= 112
ok &= all((1 + 2 * j) * 8 ** j <= 2 * (j + 1) ** 2 * 9 ** j for j in range(2000))  # sqrt((32+64j)/2^j) <= 8(j+1)(3/4)^j
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
report("P", ok, f"constants of Theorem 6.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; "
       f"K_b = {Kb:.4e}, C_1 = {C1:.4e}")

print(f"{'ALL PASS' if failures == 0 else str(failures) + ' FAILED'}")
sys.exit(1 if failures else 0)
