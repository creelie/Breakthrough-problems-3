"""Numerical check of the Gauss-sum and reciprocity identities of Lemma B.3
(Section B.3) over O = Z[w], w = exp(2 pi i/3)."""
import cmath, math, itertools, sys

W = complex(-0.5, math.sqrt(3) / 2)

class E:
    """a + b w in Z[w]."""
    __slots__ = ("a", "b")
    def __init__(s, a, b=0): s.a, s.b = int(a), int(b)
    def __add__(s, o): o = E.c(o); return E(s.a + o.a, s.b + o.b)
    def __sub__(s, o): o = E.c(o); return E(s.a - o.a, s.b - o.b)
    def __neg__(s): return E(-s.a, -s.b)
    def __mul__(s, o):
        o = E.c(o)  # w^2 = -1 - w
        return E(s.a * o.a - s.b * o.b, s.a * o.b + s.b * o.a - s.b * o.b)
    __rmul__ = __mul__
    def conj(s): return E(s.a - s.b, -s.b)       # conj(w) = w^2 = -1-w
    def norm(s): return s.a * s.a - s.a * s.b + s.b * s.b
    def cx(s): return s.a + s.b * W
    def __eq__(s, o): o = E.c(o); return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a, s.b))
    def __repr__(s): return f"({s.a}+{s.b}w)"
    @staticmethod
    def c(o): return o if isinstance(o, E) else E(o, 0)
    def divmod(s, o):
        z = s.cx() / o.cx()
        # nearest lattice point a + b w
        b = round(z.imag / (math.sqrt(3) / 2)); a = round(z.real + b / 2)
        best = None
        for da in (-1, 0, 1):
            for db in (-1, 0, 1):
                q = E(a + da, b + db); r = s - q * o
                if best is None or r.norm() < best[1].norm(): best = (q, r)
        return best
    def mod(s, o): return s.divmod(o)[1]

UNITS = [E(1), E(-1), E(0, 1), E(0, -1), E(1, 1), E(-1, -1)]  # 1,-1,w,-w,-w^2,w^2
ROOTS6 = {u: u.cx() for u in UNITS}

def primary(x):
    """unit multiple of x congruent to 1 mod 3."""
    for u in UNITS:
        y = u * x
        if y.a % 3 == 1 and y.b % 3 == 0: return y
    return None

def powmod(x, n, m):
    r, x = E(1), x.mod(m)
    while n:
        if n & 1: r = (r * x).mod(m)
        x = (x * x).mod(m); n >>= 1
    return r

def chi_p(u, p):
    """sextic symbol (u/p)_6 for a primary prime p not dividing 6, as a complex number (0 if p | u)."""
    u = E.c(u)
    if u.mod(p) == E(0): return 0
    q = p.norm(); r = powmod(u, (q - 1) // 6, p)
    for z in UNITS:
        if (r - z).mod(p) == E(0): return z.cx()
    raise ValueError("no sixth root")

def residues(n):
    """representatives of O/(n)."""
    N = n.norm(); out = []
    seen = set()
    R = int(math.isqrt(N)) * 3 + 3
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            x = E(a, b); r = x.mod(n)
            if r not in seen:
                seen.add(r); out.append(r)
                if len(out) == N: return out
    assert len(out) == N, (n, len(out), N)
    return out

def ech(z):  # e(z) = exp(4 pi i Im z / sqrt3)
    return cmath.exp(4j * math.pi * z.imag / math.sqrt(3))

def factor(n):
    return n._f

def chi_n(u, primes):
    v = 1
    for p in primes: v *= chi_p(u, p)
    return v

def gamma(j, n, primes, res):
    s = 0
    for x in res:
        c = chi_n(x, primes)
        if c == 0: continue
        s += c ** (j % 6) * ech(x.cx() / n.cx())
    return s / math.sqrt(n.norm())

# primary primes not dividing 6
PR = []
for a in range(-30, 31):
    for b in range(-30, 31):
        x = E(a, b); N = x.norm()
        if N < 5 or N > 400: continue
        if not (x.a % 3 == 1 and x.b % 3 == 0): continue
        # prime test: N prime (split) or N = p^2 with p = 2 mod 3 inert and x = +-p
        isp = N > 1 and all(N % d for d in range(2, int(math.isqrt(N)) + 1))
        if isp and N % 3 == 1: PR.append(x)
        elif x.b == 0 and abs(x.a) % 3 == 2 and all(abs(x.a) % d for d in range(2, int(math.isqrt(abs(x.a))) + 1)) and abs(x.a) > 2:
            PR.append(x)
PR = sorted(set(PR), key=lambda x: (x.norm(), x.a, x.b))
fails = 0
def ok(name, v, tol=1e-8):
    global fails
    if not v:
        fails += 1; print("FAIL", name)

alpha = lambda n: n.cx() / abs(n.cx())
lam = E(1, 2)  # 1 + 2w = i sqrt 3

def Gquad(c):
    res = residues(c); s = sum(ech((x * x).cx() / c.cx()) for x in res)
    return s / abs(c.cx())

def Gquad_formula(c):
    a, b = c.a, c.b
    return 0.5 * (1 + 1j ** (-b % 4) + 1j ** (a % 4) + 1j ** ((b - a) % 4))

cnt = 0
for p in PR:
    res = residues(p)
    g = {j: gamma(j, p, [p], res) for j in range(-1, 6)}
    ok(f"|g|=1 {p}", all(abs(abs(g[j]) - 1) < 1e-8 for j in (1, 2, 3, 4, 5, -1)))
    ok(f"g2^3=-alpha {p}", abs(g[2] ** 3 + alpha(p)) < 1e-8)
    G = complex(chi_p(4, p)).conjugate() * g[3]
    ok(f"g1g2=-alpha G {p}", abs(g[1] * g[2] + alpha(p) * G) < 1e-8)
    ok(f"g1g-1=chi(-1) {p}", abs(g[1] * g[-1] - chi_p(-1, p)) < 1e-8)
    ok(f"g2g4=1 {p}", abs(g[2] * g[4] - 1) < 1e-8)
    ok(f"Gquad(p)=g3 {p}", abs(Gquad(p) - g[3]) < 1e-8)
    ok(f"Gquad formula {p}", abs(Gquad(p) - Gquad_formula(p)) < 1e-8)
    ok(f"convert1 {p}", abs(alpha(p).conjugate() * g[2] * g[1] - (-1) * G) < 1e-8)
    ok(f"convert2 {p}", abs(-g[-1] - chi_p(-1, p) / G * alpha(p).conjugate() * g[2]) < 1e-8)
    cnt += 1
print("primes checked:", cnt, "(norms", PR[0].norm(), "to", PR[-1].norm(), ")")

# Gquad formula on non-prime c prime to 2
for a in range(-7, 8):
    for b in range(-7, 8):
        c = E(a, b)
        if c.norm() == 0 or c.norm() % 2 == 0 or c.norm() > 60: continue
        ok(f"Gquad formula {c}", abs(Gquad(c) - Gquad_formula(c)) < 1e-8)

# R table and reciprocity on pairs of distinct primes, composite Gauss sums
def cls4(c):
    """square class of c mod 4: returns (e,f) with c = (-1)^e lam^f * square mod 4."""
    for e in (0, 1):
        for f in (0, 1):
            t = E((-1) ** e) * (lam if f else E(1))
            # c / t a square mod 4?
            for x in residues(E(4)):
                if (x * x * t - c).mod(E(4)) == E(0) and (x.norm() % 2 == 1):
                    return e, f
    raise ValueError
def R(a, b):
    e, f = cls4(a); g_, h = cls4(b)
    return (-1) ** (e * h + f * g_ + f * h)

small = [p for p in PR if p.norm() < 120]
pairs = 0
for p1, p2 in itertools.combinations(small, 2):
    lhs = chi_p(p1, p2); rhs = R(p1, p2) * chi_p(p2, p1)
    ok(f"recip {p1},{p2}", abs(lhs - rhs) < 1e-8)
    ok(f"R=Gquad ratio {p1},{p2}", abs(R(p1, p2) - Gquad(p1 * p2) / (Gquad(p1) * Gquad(p2))) < 1e-8)
    G1 = complex(chi_p(4, p1)).conjugate() * Gquad(p1); G2 = complex(chi_p(4, p2)).conjugate() * Gquad(p2)
    n = p1 * p2
    if n.norm() > 3000: continue
    res = residues(n); prs = [p1, p2]
    g = {j: gamma(j, n, prs, res) for j in (-1, 1, 2, 3)}
    Gn = complex(chi_n(4, prs)).conjugate() * g[3]
    ok(f"G(ab)=G(a)G(b)R {n}", abs(Gn - G1 * G2 * R(p1, p2)) < 1e-8)
    ok(f"g2^3=mu alpha {n}", abs(g[2] ** 3 - alpha(n)) < 1e-8)
    ok(f"g1g2=mu alpha G {n}", abs(g[1] * g[2] - alpha(n) * Gn) < 1e-8)
    a1 = alpha(p1).conjugate() * gamma(2, p1, [p1], residues(p1))
    a2 = alpha(p2).conjugate() * gamma(2, p2, [p2], residues(p2))
    ok(f"crta {n}", abs(alpha(n).conjugate() * g[2] - a1 * a2 * chi_p(p1, p2) ** 4) < 1e-8)
    pairs += 1
print("composite pairs checked:", pairs)
print("FAILURES:", fails)
sys.exit(1 if fails else 0)
