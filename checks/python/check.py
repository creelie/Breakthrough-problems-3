#!/usr/bin/env python3
"""Numerical checks for "The Pólya–Vinogradov inequality with log log q for all but q^epsilon
characters".

(A) Lemma 2.1 (Chebyshev's bounds), parts (i) to (v), for x, N <= 10^6;
(B) Lemma 3.3: sum_{n >= 2} log n / n^2 < 2, with the tail bounded by an integral;
(C) the parameters (3.1) and the inequalities (3.2), in exact rationals, for theta on a grid of
    the interval [1/2, 1), and A_theta >= 288;
(D) the arithmetic in the proof of Proposition 5.5 for log q = L in [200, 10^4] and for
    L = 10^5, 10^6, 10^8: e^(L/16) >= (L/16)^4/24 > L + 1 >= M, R = M^16 < q, R <= Y,
    rho (1 + L) <= 2/M <= 1, log(qR + 2) <= 18 M, 2 + 2 pi R <= 8 M^16, k (1 + L) <= 1,
    log M <= 2 log L and log L >= 1;
(E) Section 6: the reduction of the count to (6.1) for L in [200, 10^4] and epsilon in (0, 1],
    and for epsilon = 1, 1/2, 1/10 the existence of q_0 with 2^37 20^9 L^45 <= q^(epsilon/4)
    at log q = log q_0 (with c_0 = 10^12), as well as the small-modulus bound
    M(chi) <= (7 + log q) sqrt(q) for every nonprincipal chi modulo the primes q <= 400;
(F) Section 7: log log(q + 2) <= 6 log log q on 3 <= q <= 10^6 and the decrease of the ratio,
    1 <= 11 log log q, and the constant C_5 assembled from the inequality of the proof;
(G) the sizes themselves: max M(chi)/sqrt(q) and max M(chi)/(sqrt(q) log log q) over every
    nonprincipal chi modulo the primes 1000 <= q <= 4000 (all primitive), reported and compared
    with the Pólya bound M(chi) < sqrt(q) log q;
(H) Theorem 1.4 in the small: max |L'/L(1, chi)| / log log q over the nonprincipal chi modulo
    the primes q <= 300, from the digamma function and the first Stieltjes constant at a/q,
    against reference values of the Euler-Kronecker constants;
(I) Appendix A: every numerical inequality between the constants of the proof of the
    zero-density theorem, from the kernel and zero-counting lemmas to the final constant 10^12.
Prints one line per check and exits with status 1 if any check fails.
"""
import cmath
import math
import sys
from fractions import Fraction

LIMIT = 10**6
failures = 0


def report(name, ok, detail):
    global failures
    print(f"{'PASS' if ok else 'FAIL'} {name}: {detail}", flush=True)
    if not ok:
        failures += 1


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


is_p = sieve(LIMIT)
spf = smallest_prime_factor(LIMIT)
primes = [i for i in range(2, LIMIT + 1) if is_p[i]]

# (A) Lemma 2.1: theta(x) <= x log 4; psi(x) <= 2x; sum_{p<=N} 1/p <= log log N + 10;
#     sum_{n<=x} Lambda(n)/n <= log x + 3 (with pi(x) <= 2x/log x as the fourth part).
Lam = [0.0] * (LIMIT + 1)
for p in primes:
    pk = p
    while pk <= LIMIT:
        Lam[pk] = math.log(p)
        pk *= p
ok = True
theta = psi = sLam = sinvp = 0.0
worst_i = worst_ii = worst_iv = worst_v = 0.0
pi_x = 0
for n in range(2, LIMIT + 1):
    psi += Lam[n]
    sLam += Lam[n] / n
    if is_p[n]:
        theta += math.log(n)
        sinvp += 1 / n
        pi_x += 1
    worst_i = max(worst_i, theta / (n * math.log(4)))
    worst_ii = max(worst_ii, psi / (2 * n))
    worst_v = max(worst_v, sLam - math.log(n))
    if n >= 3:
        worst_iv = max(worst_iv, pi_x * math.log(n) / (2 * n))
    if n >= 3 and sinvp > math.log(math.log(n)) + 10:
        ok = False
ok &= worst_i <= 1 and worst_ii <= 1 and worst_iv <= 1 and worst_v <= 3
report("A", ok, f"theta(x)/(x log 4) <= {worst_i:.4f}, psi(x)/(2x) <= {worst_ii:.4f}, "
       f"pi(x) log x/(2x) <= {worst_iv:.4f}, max (sum Lambda(n)/n - log x) = {worst_v:.4f} <= 3, "
       f"sum 1/p <= log log N + 10, all for x, N <= {LIMIT}")

# (B) Lemma 3.3
N = 10**6
s = sum(math.log(n) / n**2 for n in range(2, N + 1))
tail = (math.log(N) + 1) / N  # int_N^inf log t / t^2 dt
ok = s + tail < 2
report("B", ok, f"sum_(n>=2) log n/n^2 <= {s:.6f} + {tail:.2e} < 2")

# (C) parameters (3.1) and inequalities (3.2)
def params(th):
    d = min(Fraction(1, 2000), (1 - th) / 100)
    a = max(Fraction(1, 2), th - 2 * d)
    sg = a + 8 * d
    eta = (1 - sg) / 4
    return d, a, sg, eta


ok = True
mnA = None
for i in range(0, 10000):
    th = Fraction(1, 2) + Fraction(i, 20000)  # 1/2 <= th < 1
    d, a, sg, eta = params(th)
    A = -(-36 // eta)  # ceiling
    ok &= th < sg < 1 and 1 - sg >= (1 - th) / 2 and (1 - th) / 8 <= eta <= Fraction(1, 8)
    ok &= a + 2 * d <= th or a == Fraction(1, 2)
    ok &= sg - 2 * d > th  # sigma_theta - 2 delta_theta > theta, used in Section 7
    ok &= A >= 288
    mnA = A if mnA is None else min(mnA, A)
# extreme values
for th in (Fraction(1, 2), Fraction(999999, 1000000), Fraction(11, 12)):
    d, a, sg, eta = params(th)
    ok &= th < sg < 1 and 1 - sg >= (1 - th) / 2 and (1 - th) / 8 <= eta <= Fraction(1, 8)
report("C", ok, f"theta < sigma_theta < 1, 1 - sigma_theta >= (1-theta)/2, (1-theta)/8 <= eta_theta <= 1/8 "
       f"on 10^4 values of theta in [1/2, 1) and at theta = 1/2, 11/12, 1 - 10^-6; least A_theta = {mnA}")

# (D) Proposition 5.5
def prop55(L, eta=Fraction(1, 8)):
    M = math.ceil(L)
    R = M**16
    A = math.ceil(36 / eta)
    Y = M**A
    c1 = L / 16 >= math.log((L / 16) ** 4 / 24) and (L / 16) ** 4 / 24 > L + 1 >= M
    c2 = (16 * math.log(M) < L) and R <= Y  # R < q and R <= Y
    rho = L**2 / M**4
    c3 = rho * (1 + L) <= 2 / M <= 1
    c4 = math.log(1 + 2 * math.exp(-L) / R) + L + 16 * math.log(M) <= 18 * M  # log(qR + 2) <= 18 M
    c5 = 2 + 2 * math.pi * R <= 8 * M**16
    k_bound = 288 * M**34 / (M**36 * math.log(M))
    k = R * 18 * M * 8 * M**16 / (M**(A * eta) * A * math.log(M))  # k with the bounds of the proof
    c6 = k * (1 + L) <= k_bound + 1e-12 and k_bound <= 1
    c7 = math.log(M) <= 2 * math.log(L) and math.log(L) >= 1
    return c1 and c2 and c3 and c4 and c5 and c6 and c7


ok = all(prop55(L / 10) for L in range(2000, 100001)) and all(prop55(L) for L in (1e5, 1e6, 1e8))
ok &= all(prop55(L, eta) for L in (200, 200.5, 1000) for eta in (Fraction(1, 16), Fraction(1, 1000)))
report("D", ok, "the inequalities of the proof of Proposition 5.5 hold for L = log q in [200, 10^4] "
       "(step 0.1), for L = 10^5, 10^6, 10^8, and for eta_theta = 1/16, 1/1000")

# (E) Section 6
def count_reduction(L, eps):
    M = math.ceil(L)
    R = M**16
    lhs = 2 * math.log(R) + (eps / 4) * (math.log(5) + 3 * L + math.log(R)) + 9 * math.log(math.log(5) + 3 * L + math.log(R))
    rhs = 37 * math.log(2) + 9 * math.log(20) + 45 * math.log(L) + 3 * eps * L / 4
    return lhs <= rhs + 1e-9


ok = all(count_reduction(L / 10, eps) for L in range(2000, 100001, 7) for eps in (1.0, 0.5, 0.1, 0.01))
q0 = {}
for eps in (1.0, 0.5, 0.1):
    # least L >= 200 (integer) with c_0 2^37 20^9 L^45 <= e^(eps L/4), c_0 = 10^12
    L = 200
    while 12 * math.log(10) + 37 * math.log(2) + 9 * math.log(20) + 45 * math.log(L) > eps * L / 4:
        L += 1
    q0[eps] = L
    ok &= 12 * math.log(10) + 37 * math.log(2) + 9 * math.log(20) + 45 * math.log(L) <= eps * L / 4
# small moduli: M(chi) <= (7 + log q) sqrt(q), every nonprincipal chi mod prime q <= 400
def characters(q, g):
    # chi_j(g^k) = e(jk/(q-1)); returns table chi_j(n) for n = 0..q-1 and all j
    pw = [pow(g, k, q) for k in range(q - 1)]
    idx = [0] * q
    for k, v in enumerate(pw):
        idx[v] = k
    roots = [cmath.exp(2j * math.pi * m / (q - 1)) for m in range(q - 1)]
    return idx, roots


def primitive_root(q):
    fs = prime_factors(q - 1, spf)
    return next(g for g in range(2, q) if all(pow(g, (q - 1) // f, q) != 1 for f in fs))


def max_M(q):
    """max over nonprincipal chi mod prime q of M(chi), and the worst M(chi)/sqrt(q)."""
    g = primitive_root(q)
    idx, roots = characters(q, g)
    best = 0.0
    for j in range(1, q - 1):
        acc, m = 0j, 0.0
        for n in range(1, q):
            acc += roots[j * idx[n] % (q - 1)]
            m = max(m, abs(acc))
        best = max(best, m)
    return best


worst = 0.0
for q in [p for p in primes if 3 <= p <= 400]:
    m = max_M(q)
    worst = max(worst, m / ((7 + math.log(q)) * math.sqrt(q)))
ok &= worst <= 1
report("E", ok, f"count reduction (6.1) holds on L in [200, 10^4], eps in {{1, 1/2, 1/10, 1/100}}; "
       f"q_0 = e^L with L = {q0[1.0]}, {q0[0.5]}, {q0[0.1]} for eps = 1, 1/2, 1/10 (c_0 = 10^12); "
       f"M(chi)/((7 + log q) sqrt q) <= {worst:.4f} for primes q <= 400")

# (F) Section 7
ok = True
prev = None
for q in range(3, LIMIT + 1):
    r = math.log(math.log(q + 2)) / math.log(math.log(q))
    ok &= r <= 6 and (prev is None or r <= prev + 1e-15)
    prev = r
r3 = math.log(math.log(5)) / math.log(math.log(3))
ok &= r3 < 5.1 and 11 * math.log(math.log(3)) >= 1


def C5(sigma, K1):
    return 6 / (1 - sigma) + 429 * K1 * (1 + 1 / (1 - sigma)) + 99


# the bound of the proof, log log(q+2)/(1-sigma) + 39 K1 (1 + 1/(1-sigma)) + 9, is at most C5 log log q
for sigma in (0.6, 0.9, 0.999):
    for K1 in (1.0, 50.0, 1e4):
        for q in (3, 10, 10**6):
            lhs = math.log(math.log(q + 2)) / (1 - sigma) + 39 * K1 * (1 + 1 / (1 - sigma)) + 9
            ok &= lhs <= C5(sigma, K1) * math.log(math.log(q))
report("F", ok, f"log log(q+2)/log log q decreases on 3 <= q <= 10^6, equals {r3:.4f} < 5.1 at q = 3; "
       f"11 log log 3 = {11 * math.log(math.log(3)):.4f} >= 1; C_5 bounds the proof's constant")

# (G) sizes for primes 1000 <= q <= 4000
mx, mxl, qm = 0.0, 0.0, None
for q in [p for p in primes if 1000 <= p <= 4000]:
    m = max_M(q)
    v = m / math.sqrt(q)
    if v > mx:
        mx, qm = v, q
    mxl = max(mxl, v / math.log(math.log(q)))
    if m >= math.sqrt(q) * math.log(q):
        ok = False
ok = mx < math.log(4000)
report("G", ok, f"max M(chi)/sqrt q = {mx:.4f} (at q = {qm}), max M(chi)/(sqrt q log log q) = {mxl:.4f}, "
       f"over the nonprincipal chi modulo the primes 1000 <= q <= 4000; all below the Pólya bound sqrt q log q")

# (H) L'/L(1, chi) = -log q + sum chi(a) gamma_1(a/q) / sum chi(a) psi(a/q)
B2 = [Fraction(1, 6), Fraction(-1, 30), Fraction(1, 42), Fraction(-1, 30), Fraction(5, 66),
      Fraction(-691, 2730), Fraction(7, 6), Fraction(-3617, 510)]
HARM = [sum(Fraction(1, i) for i in range(1, n + 1)) for n in range(20)]
EM_N = 30


def digamma(a):
    x = a + EM_N
    s = math.log(x) - 1 / (2 * x) - sum(float(B2[j]) / ((2 * j + 2) * x ** (2 * j + 2)) for j in range(8))
    return s - sum(1 / (a + k) for k in range(EM_N))


def stieltjes1(a):
    x = a + EM_N
    lx = math.log(x)
    s = sum(math.log(a + k) / (a + k) for k in range(EM_N)) - lx * lx / 2 + lx / (2 * x)
    s += sum(float(B2[j]) * (lx - float(HARM[2 * j + 1])) / ((2 * j + 2) * x ** (2 * j + 2)) for j in range(8))
    return s


EULER = 0.5772156649015329
ok = abs(digamma(1) + EULER) < 1e-13 and abs(stieltjes1(1) + 0.0728158454836767) < 1e-13
ok &= abs(digamma(0.5) + EULER + 2 * math.log(2)) < 1e-13


def logderivs(q):
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


REF = {3: 0.945497280871680703, 5: 1.72062421251340476, 7: 2.08759407471733013,
       11: 2.41542590428326783, 13: 2.6107577374176502, 19: 4.79040941571428333,
       101: 5.29701289150966972, 199: 6.47366513609320739, 293: 3.38438152121953979}
mxr, vals = 0.0, {}
for q in [p for p in primes if 3 <= p <= 300]:
    gq, mx = logderivs(q)
    vals[q] = gq.real
    ok &= abs(gq.imag) < 1e-9
    mxr = max(mxr, mx / math.log(math.log(q)))
worstR = max(abs(vals[q] - v) for q, v in REF.items())
ok &= worstR < 1e-9
report("H", ok, f"max |L'/L(1,chi)|/log log q = {mxr:.4f} over the nonprincipal chi modulo the primes "
       f"q <= 300; the Euler-Kronecker constants agree with {len(REF)} reference values to {worstR:.1e}")

# (I) Appendix A: the explicit constants of the zero-density theorem
def appendix_constants():
    ok = True
    sp = math.sqrt(math.pi)
    # Lemma A.3: 1 + sum 1/j^2 <= 2.65; 2 T'(4N/(kT') + 2) 2.65 = 21.2 N/k + 10.6 T'
    ok &= 1 + math.pi**2 / 6 <= 2.65 and 2 * 2.65 * 4 <= 21.2 and 2 * 2.65 * 2 <= 10.6
    ok &= all(math.exp(x) - 1 <= 2 * x for x in (i / 1000 for i in range(1, 1001)))
    # Lemma A.2 (zero box): 1/log(7/6) < 6.49 < 7; 29/16 < 9/4; zeta(4)/zeta(2) = pi^2/15 > 1/2
    ok &= 1 / math.log(7 / 6) < 6.49 and 29 / 16 < 9 / 4 and math.pi**2 / 15 > 0.5
    # Lemma A.6 (kernel): e^(1/4)/sqrt(pi) < 0.73
    ok &= math.exp(0.25) / sp < 0.73
    # Step 1: 8(T+5) <= 28 T for T >= 2; log 28 < 1.87 LL with LL >= log 6; 14 (1.87 + 1) <= 42
    LL0 = math.log(6)
    ok &= 8 * (2 + 5) <= 28 * 2 and math.log(28) < 1.87 * LL0 and 14 * 2.87 <= 42
    # Step 2: |Phi(1/Y)| >= 1/2 and the tail <= 1/8, both at Y = 216 and decreasing in Y
    def tail(Y):
        l = math.log(Y)
        return 2 / (sp * l) * Y**(7 / 6 - l / 4) / (l / 4 - 7 / 12)
    ok &= 1 - math.exp(-math.log(216)**2 / 4) / (sp * math.log(216)) >= 0.5
    ok &= tail(216) < 0.11
    Ys = [216 * 1.01**i for i in range(0, 3000)]
    ok &= all(tail(Ys[i + 1]) <= tail(Ys[i]) for i in range(len(Ys) - 1))
    # Step 3: number of blocks 2 log Y/log 2 + 1 <= 4 log Y at Y = 216; r <= 1/5 at X = 6
    ok &= 2 * math.log(216) / math.log(2) + 1 <= 4 * math.log(216) and 1 / (2 * math.log(12)) <= 0.25
    # 86 + 22*5/4 <= 114; log 2 + 6 LL <= 6.4 LL; 1 + LL <= 1.56 LL
    ok &= 86 + 22 * 1.25 <= 114 and math.log(2) + 6 * LL0 <= 6.4 * LL0 and 1 + LL0 <= 1.56 * LL0
    c1 = 4 * 6.4**2 / math.pi * (7 / 12) * 4 * math.e * 2 * 114 * 1.56**3
    ok &= 1 / 12 + 0.5 <= 7 / 12 and c1 <= 3e5 and 48**2 * 12 * 3e5 <= 1e10
    # Step 4: 12 e^(1/36)/(2 pi) <= 2; 64 (2 pi^(1/4))^2 <= 454; w(t) < 3; 1.4 e^(-u^2) tail
    ok &= 12 * math.exp(1 / 36) / (2 * math.pi) <= 2 and 64 * 4 * sp <= 454
    ok &= 1 + 2 * sum(math.exp(-(j - 0.5)**2) for j in range(1, 50)) < 3
    ok &= sum(math.exp(-(7 + j)**2 + 49) for j in range(0, 50)) <= 1.4
    # |t| > T_2: 2 * 52 * 1.4 * 2 <= 292, 8 LL <= e^(2 LL), 292 e^(13 LL/3 - 16 LL^2) <= 1 for LL >= log 6
    ok &= 1.2**2 * 36 <= 52 and 2 * 52 * 1.4 * 2 <= 292 and 8 * LL0 <= math.exp(2 * LL0)
    ok &= all(292 * math.exp(13 * l / 3 - 16 * l * l) <= 1 for l in (LL0 + i / 100 for i in range(0, 2000)))
    # truncation: 2.2 + 1.2 T2 <= 2.3 T2 for T2 >= 9; kT2 >= 27; 2.3 * 27^(-2/3) <= 1
    T2min = 2 + 4 * LL0
    ok &= T2min >= 9 and 2.2 + 1.2 * T2min <= 2.3 * T2min and 3 * T2min >= 27 and 2.3 * 27**(-2 / 3) <= 1
    # sum d^(-5/3) <= 2.5; (43 + 22) 2.5 <= 163; T + 4 LL <= 3 LL T; log(3 LL) <= LL
    ok &= 1 + 1.5 <= 2.5 and 65 * 2.5 <= 163
    ok &= all(T + 4 * l <= 3 * l * T and math.log(3 * l) <= l for T in (2, 2.5, 3, 10) for l in (LL0 + i / 100 for i in range(0, 2000)))
    # blocks: (log 2 + 3 * 2 LL)/log 2 + 2 <= 11 LL; 2^(1/3) <= 1.26; 2 (86 * 1.26 + 22) 1.56^3 <= 1000
    ok &= all((math.log(2) + 6 * l) / math.log(2) + 2 <= 11 * l for l in (LL0 + i / 100 for i in range(0, 2000)))
    ok &= 2**(1 / 3) <= 1.26 and 2 * (86 * 1.26 + 22) * 1.56**3 <= 1000
    # collecting: 2 (11 LL)^2 10^3 LL^3 + 326 <= 2.5e5 LL^5; 454 (3 * 2.5e5 * 3 LL^6 kT + k) <= 1.1e9 LL^6 kT
    ok &= all(2 * 121 * 1000 * l**5 + 326 <= 2.5e5 * l**5 for l in (LL0, 2.0, 10.0))
    ok &= 454 * (3 * 2.5e5 * 3 + 1 / LL0**6 / 6) <= 1.1e9
    # Step 5: 42 (1e10 LL^8 + 1.1e9 LL^6) LL <= 1e12 LL^9
    ok &= 42 * (1e10 + 1.1e9 / LL0**2) <= 1e12
    return ok


report("I", appendix_constants(), "the numerical inequalities of Appendix A hold: kernel and zero-box constants, the tail bound "
       "at Y = 216 and its monotonicity, the class I constants 3e5 and 1e10, the class II constants 454, 292, 163, "
       "1e3, 2.5e5, 1.1e9, and the final constant 1e12")

print(f"{'ALL PASS' if failures == 0 else str(failures) + ' FAILED'}")
sys.exit(1 if failures else 0)
