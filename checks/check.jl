# Numerical checks in Julia for "The Pólya–Vinogradov inequality with log log q".
# The same checks (A) to (M) as check.py, written independently:
# (A) Lemma 2.1 (Chebyshev's bounds) for x, N <= 10^6;
# (B) Lemma 2.2: the Selberg weights satisfy lambda_1 = 1, |lambda_d| <= 1 and Q = 1/S, in exact
#     rationals, and the sieve bound holds for a_n = n(n + 2);
# (C) Lemmas 3.3, 3.4 and 3.6 on grids and for random polynomials;
# (D) the exponent arithmetic of Section 3 and of the proof of Theorem 1.3(ii), in exact rationals;
# (E) Corollary 3.8: the identity for T(x + h) - T(x), the inequalities used for h = x^(47/50),
#     and max |sum_{p<=x} xi(p) log p| / (x^(19/20) log(k+2)) for quadratic xi, x <= 10^6;
# (F) Lemmas 4.2 and 4.3 on random data;
# (G) Lemma 4.4 for characters and random completely multiplicative f;
# (H) Lemma 4.5: prime pairs for X <= 10^5 and even 2 <= h <= 100, the sieve remainders, and
#     the fourth moment of G(h);
# (I) the constants and the parameters I, J in the proof of Theorem 4.1;
# (J) Lemma 5.1 for primes q <= 20000 and the bound |r(theta)| < 3;
# (K) Lemma 5.2, the sum of m^(-19/20) in Lemma 5.3, and Proposition 5.4;
# (L) Lemmas 6.2 and 6.3: block counts for primes 101 <= q <= 401 and the inequalities;
# (M) Theorem 1.3: L'/L(1, chi) for every nonprincipal chi modulo the primes q <= 1000 from the
#     Hurwitz zeta function at s = 1, and the Euler-Kronecker constants against mpmath.
# Exit status 1 if a check fails.

const LIMIT = 10^6
const XL = 4 * LIMIT

function sieve(n)
    isp = trues(n)
    isp[1] = false
    for i in 2:isqrt(n)
        if isp[i]
            for j in i*i:i:n
                isp[j] = false
            end
        end
    end
    isp
end

function smallest_prime_factor(n)
    spf = collect(0:n)
    for i in 2:isqrt(n)
        if spf[i+1] == i
            for j in i*i:i:n
                spf[j+1] == j && (spf[j+1] = i)
            end
        end
    end
    spf
end

const ISP = sieve(XL)
const SPF = smallest_prime_factor(LIMIT)
spf(n) = SPF[n+1]
isp(n) = n >= 2 && ISP[n]
const PRIMES = [p for p in 2:LIMIT if ISP[p]]

function prime_factors(n)
    out = Int[]
    while n > 1
        p = spf(n)
        push!(out, p)
        while n % p == 0
            n ÷= p
        end
    end
    out
end

legendre(n, q) = (r = powermod(mod(n, q), (q - 1) ÷ 2, q); r == 0 ? 0 : (r == 1 ? 1 : -1))

const STATE = Ref{UInt64}(12345)
function rnd()
    STATE[] = STATE[] * 0x5851f42d4c957f2d + 0x14057b7ef767814f
    (STATE[] >> 11) / 2.0^53
end
rint(x) = floor(Int, x)
ex(t) = cis(2π * t)

fails = 0
function report(name, ok, detail)
    println(ok ? "PASS " : "FAIL ", name, ": ", detail)
    flush(stdout)
    ok || (global fails += 1)
end

# (A) Lemma 2.1
function checkA()
    ok, θ, ψ, sl, sr = true, 0.0, 0.0, 0.0, 0.0
    w1 = w2 = w3 = 0.0
    for n in 2:LIMIT
        p = spf(n)
        m = n
        while m % p == 0
            m ÷= p
        end
        if m == 1
            ψ += log(p)
            if n == p
                θ += log(p)
                sl += log(p) / p
                sr += 1 / p
            end
        end
        w1 = max(w1, θ / (n * log(4)))
        w2 = max(w2, (ψ - θ) / (2 * sqrt(n) * log(n)))
        w3 = max(w3, ψ / (4n))
        ok &= sl <= log(n) + log(4) && sr <= log(log(n)) + 10
    end
    ok &= w1 <= 1 && w2 <= 1 && w3 <= 1
    ok, w1, w2, w3
end
okA, w1, w2, w3 = checkA()
report("A", okA, "theta(x) <= x log 4 (max ratio $(round(w1, digits = 4))), psi - theta <= 2 sqrt(x) log x " *
       "($(round(w2, digits = 4))), psi(x) <= 4x ($(round(w3, digits = 4))), (iii) and (iv) for x, N <= 10^6")

# (B) Lemma 2.2 in exact rationals
const Q = Rational{BigInt}
function selberg(ps, nup, y)
    divs = [1]
    for p in ps
        divs = vcat(divs, [d * p for d in divs])
    end
    D = sort([d for d in divs if d * d <= y])
    fac = Dict(d => [p for p in ps if d % p == 0] for d in divs)
    nu(d) = prod((nup(p) for p in fac[d]); init = one(Q))
    g(d) = prod((nup(p) / (1 - nup(p)) for p in fac[d]); init = one(Q))
    S = sum(g(l) for l in D)
    lam = Dict{Int,Q}()
    for d in D
        tot = sum((g(e) for e in D if gcd(e, d) == 1 && (d * e)^2 <= y); init = zero(Q))
        lam[d] = (-1)^length(fac[d]) * g(d) / (nu(d) * S) * tot
    end
    D, lam, S, nu
end

function checkB()
    ok, cases = true, 0
    for (ps, nup) in [([2, 3, 5, 7, 11, 13], p -> Q(1, p)), ([3, 5, 7, 11, 13, 17], p -> Q(2, p)),
                      ([2, 5, 7, 13, 19], p -> Q(1, p + 1))]
        for y in [1, 4, 30, 200, 3000, 10^5]
            D, lam, S, nu = selberg(ps, nup, y)
            Qf = sum(lam[a] * lam[b] * nu(lcm(a, b)) for a in D for b in D)
            ok &= lam[1] == 1 && all(abs(v) <= 1 for v in values(lam)) && Qf * S == 1
            cases += 1
        end
    end
    for X in [100, 1000, 10^4]
        for (z, y) in [(5, 30), (7, 60), (11, 150), (13, 200)]
            ps = [p for p in [3, 5, 7, 11, 13] if p <= z]
            D, lam, S, nu = selberg(ps, p -> Q(2, p), y)
            P = prod(ps)
            cnt = count(n -> gcd(n * (n + 2), P) == 1, 0:X-1)
            err = zero(Q)
            for d in 1:y
                P % d == 0 || continue
                k = count(p -> d % p == 0, ps)
                Rd = count(n -> (n * (n + 2)) % d == 0, 0:X-1) - Q(2^k, d) * X
                err += 3^k * abs(Rd)
            end
            ok &= cnt <= X / S + err
            cases += 1
        end
    end
    ok, cases
end
okB, casesB = checkB()
report("B", okB, "lambda_1 = 1, |lambda_d| <= 1, Q = 1/S and the sieve bound in $casesB cases, exact")

# (C) Lemmas 3.3, 3.4 and 3.6
function checkC()
    ok, worst = true, 0.0
    for i in 1:400, k in 0:359
        w = (i / 800) * cis(π * k / 180)
        worst = max(worst, abs(log(1 - w)) / abs(w))
    end
    ok &= worst <= 1.5
    for _ in 1:400
        deg = 1 + rint(6 * rnd())
        co = [complex(2 * rnd() - 1, 2 * rnd() - 1) for _ in 0:deg]
        c = complex(2 * rnd() - 1, 2 * rnd() - 1)
        R = 0.2 + 2 * rnd()
        r = R * (0.05 + 0.9 * rnd())
        h(z) = sum(co[j+1] * z^j for j in 0:deg)
        hc = h(c)
        A = maximum(real(h(c + R * cis(2π * k / 720)) - hc) for k in 0:719)
        lhs = maximum(abs(h(c + r * cis(2π * k / 360)) - hc) for k in 0:359)
        ok &= lhs <= 2r / (R - r) * A * (1 + 1e-6) + 1e-12
    end
    for qq in [1, 2, 3, 10, 1000, 10^9], k in 0:4000
        t = 10^(k / 500) - 1
        ok &= log(2qq * (3 + t)^2) <= 10 * log(qq + 2) * sqrt(1 + t)
        for σ in [0.5, 0.7, 1.0, 2.0, 5.0]
            s = complex(σ, t)
            ok &= abs(s * (s + 1)) >= (1 + t)^2 / 8
        end
    end
    ok, worst
end
okC, worstC = checkC()
A0 = 1.5 * sum(p^-1.5 for p in PRIMES)
report("C", okC, "|log(1-w)| <= 1.5|w| on |w| <= 1/2 (max ratio $(round(worstC, digits = 4))), " *
       "A_0 = $(round(A0, digits = 5)); Borel-Caratheodory for 400 random polynomials; Lemma 3.6 on grids")

# (D) exponents
δ, a = 1 // 2000, 7 // 8 - 1 // 1000
σ0 = a + 8δ
okD = 0 < δ < 1 // 1000 && 1 // 2 <= a <= 1 && a + 2δ == 7 // 8
okD &= σ0 == 7 // 8 + 3 // 1000 && 1 + σ0 - 47 // 50 < 19 // 20
okD &= 17 * (σ0 - 1) < -2 && 2.0^float(1 + σ0) <= 4
report("D", okD, "sigma_0 = $σ0 = 7/8 + 3/1000, 1 + sigma_0 - 47/50 = $(1 + σ0 - 47 // 50) < 19/20, " *
       "17(sigma_0 - 1) = $(17 * (σ0 - 1)) < -2")

# (E) Corollary 3.8
function checkE()
    ok, cases = true, 0
    for q in [3, 5, 101]
        lam = zeros(3000)
        for n in 2:3000
            p = spf(n)
            m = n
            while m % p == 0
                m ÷= p
            end
            m == 1 && (lam[n] = legendre(n, q) * log(p))
        end
        T(y) = sum((lam[n] * (y - n) for n in 1:floor(Int, y)); init = 0.0)
        for _ in 1:40
            x = 1 + 1400 * rnd()
            h = x * rnd()
            fx, fxh = floor(Int, x), floor(Int, x + h)
            lhs = T(x + h) - T(x)
            rhs = h * sum(lam[1:fx]) + sum((lam[n] * (x + h - n) for n in fx+1:fxh); init = 0.0)
            ok &= abs(lhs - rhs) <= 1e-7 * (1 + abs(lhs)) && fxh - fx <= h + 1
            cases += 1
        end
    end
    for k in 0:6000
        x = 10^(k / 100)
        ok &= log(2x) <= 1 + 100 * x^0.01 && 2 * sqrt(x) * log(x) <= 200 * x^0.95
    end
    worst = 0.0
    for q in [3, 5, 7, 11, 13, 101, 997]
        run = 0.0
        for p in PRIMES
            run += legendre(p, q) * log(p)
            worst = max(worst, abs(run) / (p^0.95 * log(q + 2)))
        end
    end
    ok, cases, worst
end
okE, casesE, worstE = checkE()
report("E", okE, "T(x+h) - T(x) identity in $casesE cases, log(2x) <= 1 + 100 x^(1/100), " *
       "2 sqrt(x) log x <= 200 x^(19/20); max |sum xi(p) log p| / (x^(19/20) log(k+2)) = $(round(worstE, digits = 4))")

dist(x) = abs(x - round(x))
wM(M, θ) = (d = dist(θ); d < 1 / M ? M : 1 / d)

# (F) Lemmas 4.2 and 4.3
function checkF()
    ok, cases = true, 0
    for _ in 1:3000
        r = 2 + rint(400 * rnd())
        a = rint(r * rnd())
        while gcd(a, r) != 1
            a = (a + 1) % r
        end
        α = a / r + (2 * rnd() - 1) / r^2 + rint(20 * rnd()) - 10
        for k in 1:r÷2
            ok &= dist(k * α) >= 1 / (2r) - 1e-12
        end
        H = rint(1000 * rnd())
        ds = [dist(h * α) for h in 1:H]
        for _ in 1:3
            t = 0.5 * rnd()
            ok &= count(d -> d < t, ds) <= (4H / r + 1) * (4r * t + 1)
        end
        M = 0.5 + 1000 * rnd()
        K = max(0, ceil(Int, log2(M)))
        ws = [d < 1 / M ? M : 1 / d for d in ds]
        ok &= sum(ws; init = 0.0) <= (4H / r + 1) * (3M + 4r + 8r * K)
        ok &= sum((w * w for w in ws); init = 0.0) <= (4H / r + 1) * (20r * M + 3M * M)
        cases += 1
    end
    for _ in 1:2000
        θ = 2 * rnd() - 1
        U = 0.5 + 300 * rnd()
        A = rint(1000 * rnd())
        B = A + rint(U * rnd())
        S = sum((ex(x * θ) for x in A+1:B); init = 0.0im)
        ok &= abs(S) <= wM(U, θ) * (1 + 1e-9)
    end
    for _ in 1:300
        α = rnd()
        U = 1 + 50 * rnd()
        A = rint(100 * rnd())
        B = A + rint(U)
        N = rint(2000 * rnd()) + 1
        nV = 1 + rint(20 * rnd())
        V = sort(unique([1 + rint(60 * rnd()) for _ in 1:nV]))
        b = Dict{Int,ComplexF64}()
        for v in V
            b[v] = ex(rnd()) * rnd()
        end
        lhs = sum(abs(sum((b[v] * ex(u * v * α) for v in V if u * v <= N); init = 0.0im))^2 for u in A+1:B)
        rhs = sum(abs(b[v]) * abs(b[w]) * wM(U, (v - w) * α) for v in V for w in V)
        ok &= lhs <= rhs * (1 + 1e-9) + 1e-9
        Hh = rint(80 * rnd())
        Mm = 0.5 + 100 * rnd()
        lhs = sum((wM(Mm, (m - m2) * α) for m in 1:Hh for m2 in 1:Hh); init = 0.0)
        ok &= lhs <= Hh * (Mm + 2 * sum((wM(Mm, h * α) for h in 1:Hh); init = 0.0)) * (1 + 1e-12)
    end
    ok, cases
end
okF, casesF = checkF()
report("F", okF, "Lemma 4.2 (i)-(iii) for $casesF random (alpha, a/r), Lemma 4.3 (i) at 2000 and (ii), (iii) " *
       "at 300 random cases")

# (G) Lemma 4.4
const ZETA32 = 2.612375348685488
const C5 = 1 + 4 * ZETA32
function checkG()
    ok, worst = true, 0.0
    for trial in 0:59
        N = 2 + rint(2998 * rnd())
        α = rnd()
        f = zeros(ComplexF64, N)
        if trial % 3 == 0
            q = [3, 5, 7, 11, 101, 997][(trial ÷ 3) % 6 + 1]
            for n in 1:N
                f[n] = legendre(n, q)
            end
        else
            fp = Dict{Int,ComplexF64}()
            f[1] = 1
            for n in 2:N
                p = spf(n)
                haskey(fp, p) || (fp[p] = ex(rnd()) * (trial % 3 == 2 ? rnd() : 1.0))
                f[n] = fp[p] * f[n÷p]
            end
        end
        S = sum(f[n] * ex(n * α) for n in 1:N)
        T = 0.0im
        for p in 2:N
            spf(p) == p || continue
            T += log(p) * f[p] * sum(f[m] * ex(p * m * α) for m in 1:N÷p)
        end
        err = abs(S * log(N) - T) / N
        worst = max(worst, err)
        ok &= err <= C5
    end
    ok, worst
end
okG, worstG4 = checkG()
report("G", okG, "Lemma 4.4 for 60 completely multiplicative f, N <= 3000: max error / N = " *
       "$(round(worstG4, digits = 4)) <= C_5 = $(round(C5, digits = 4))")

# (H) Lemma 4.5
Gfun(h) = prod((p / (p - 1) for p in prime_factors(h)); init = 1.0)
function checkH()
    ok, worst = true, 0.0
    XO = 10^5
    for h in 2:2:100
        g2 = Gfun(h)^2
        bound(X) = 400 * g2 * X / log(X)^2 + 3 * X^0.6
        cnt = 0
        for X in 2:XO
            n = X - 1
            jump = isp(n) && isp(n + h)
            jump && (cnt += 1)
            if jump || X <= 8
                ok &= cnt <= bound(X)
                worst = max(worst, cnt / bound(X))
            end
        end
    end
    for X in [1, 2, 7, 100, 1001, 2000], h in [2, 4, 6, 30, 98]
        for d in [1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 3 * 5 * 7 * 11]
            gcd(d, h) == 1 || continue
            k = count(p -> d % p == 0, [3, 5, 7, 11, 13])
            c = count(n -> (n * (n + h)) % d == 0, 0:X-1)
            ok &= abs(c - 2^k * X / d) <= 2^k && 6^k <= d * d
        end
    end
    for X in 2:10^5-1
        T = round(Int, X^0.05)
        while T^20 > X
            T -= 1
        end
        while (T + 1)^20 <= X
            T += 1
        end
        ok &= (T + 1)^20 > X
    end
    for m in 1:10^5-1
        n, τ, Ω = m, 1, 0
        while n > 1
            p, e = spf(n), 0
            while n % p == 0
                n ÷= p
                e += 1
            end
            τ *= e + 1
            Ω += e
        end
        ok &= τ <= 2^Ω
    end
    acc, worstG = 0.0, 0.0
    for h in 1:XO
        acc += Gfun(h)^4
        worstG = max(worstG, acc / h)
    end
    ok &= worstG <= exp(30) && π^2 / 6 - 1 <= 1
    ok &= all(Int128(t + 1)^5 <= Int128(t + 31) * Int128(t)^4 for t in 1:10^5-1)
    ok, worst, worstG
end
okH, worstH, worstGH = checkH()
report("H", okH, "prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, even 2 <= h <= 100 " *
       "(max ratio $(round(worstH, digits = 4))); |R_d| <= 2^omega(d); tau(m) <= 2^Omega(m); " *
       "max_X X^-1 sum G(h)^4 = $(round(worstGH, digits = 3)) <= e^30")

# (I) constants and parameters in the proof of Theorem 4.1
function checkI()
    ok = 64 * log(2) < 45
    for ell in 64:10^4
        I = ndigits(ell, base = 2)
        J = ell + 1 - 4I
        ok &= big(16)^I > big(ell)^4 && 1 <= J <= ell && 4I <= ell && 2^I <= 2ell
        ok &= big(2)^J * big(16)^I == big(2)^(ell + 1)
        ok &= big(J)^2 * big(2)^J * big(ell)^4 <= big(ell + 1)^2 * big(2)^(ell + 1) && (ell + 1)^2 <= big(ell)^4
    end
    ok &= 1 / log(2) <= 2
    ok &= (7 // 4) / (1 // 4)^3 == 112
    ok &= all((1 + 2j) * big(8)^j <= 2 * (j + 1)^2 * big(9)^j for j in 0:1999)
    ok &= all(sum(2^(j / 2) for j in 0:J-1) <= 3 * 2^(J / 2) for J in 1:199)
    ok &= 3 * sqrt(14) <= 12 && sqrt(24) <= 5 && 8 * 112 + 12 == 908
    ok &= 6 * 225 == 1350 <= 37^2 && 15 + 37 == 52
    coeffs = [320 * 15^3, 48 * 15^4, 80 * 15^3, 180 * 15^3]
    ok &= all(c <= 40^4 for c in coeffs) && 2^0.25 <= 2
    ok &= 2^0.3 <= 2 && 2 + 16 + 32 * 2 * 15^3 == 216018
    ok &= all(log(x) <= 15 * x^(1 / 15) for x in [1 + 10^(k / 10) for k in 0:2999])
    ok &= all(log(x) <= 4 * x^0.25 for x in [1 + 10^(k / 10) for k in 0:2999])
    lg = 0.0
    for N in 1:10^4-1
        lg += log(N)                       # log N!
        ok &= N * log(N) - lg <= N
    end
    pl = sum(log(p) / (p * (p - 1)) for p in PRIMES)
    ok &= pl <= 2 * sum(log(p) / p^2 for p in PRIMES) <= 2 * ZETA32
    ok
end
okI = checkI()
Kb = 80 * sqrt(800 * exp(15)) + 52
C1 = 45 + C5 + 908 + 216018 * Kb + 60 + 2Kb
report("I", okI, "constants of Theorem 4.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; " *
       "K_b = $(round(Kb, sigdigits = 5)), C_1 = $(round(C1, sigdigits = 5))")

# (J) Lemma 5.1
function quad_table(q)
    tab = fill(-1, q)
    tab[1] = 0                             # tab[a + 1] = (a/q)
    for a in 1:q-1
        tab[(a * a) % q + 1] = 1
    end
    tab
end
function checkJ()
    ok, worstτ, nq, worstratio = true, 0.0, 0, 0.0
    for q in 3:20000
        isp(q) || continue
        tab = quad_table(q)
        run, m = 0, 0
        for n in 1:q-1
            run += tab[n+1]
            m = max(m, abs(run))
        end
        if q <= 3000
            τ = sum(tab[a+1] * cis(2π * a / q) for a in 1:q-1)
            worstτ = max(worstτ, abs(abs(τ)^2 - q) / q)
            b0 = sum(1 / k for k in 1:q÷2)
            ok &= m <= sqrt(q) * (b0 + 6)
            nq += 1
        end
        q >= 1000 && (worstratio = max(worstratio, m / (sqrt(q) * log(log(q)))))
    end
    worst = 0.0
    for k in 1:500000, θ in (k / 10^6, -k / 10^6)
        r = 1 / (1 - cis(-2π * θ)) - 1 / (2π * im * θ)
        worst = max(worst, abs(r))
    end
    ok &= worstτ < 1e-9 && worstratio < 2 && worst < 3
    ok, worstτ, nq, worstratio, worst
end
okJ, worstτ, nqJ, ratioJ, worstr = checkJ()
report("J", okJ, "|tau|^2 = q (max rel. error $(round(worstτ, sigdigits = 2))) and max|S| <= sqrt(q)(B+6) for " *
       "$nqJ primes; max ratio for 1000 <= q <= 20000: $(round(ratioJ, digits = 4)); " *
       "max |r(theta)| = $(round(worstr, digits = 6)) < 3")

# (K) Lemma 5.2, Lemma 5.3, Proposition 5.4
function checkK()
    ok, prd, worstS = true, 1.0, 0.0
    for Y in 2:LIMIT
        isp(Y) && (prd /= 1 - 1 / Y)
        worstS = max(worstS, prd / (exp(11) * log(Y)))
    end
    ok &= worstS <= 1
    s19 = 0.0
    for m in 1:10^6
        s19 += m^-0.95
        (m % 997 == 0 || m < 100) && (ok &= s19 <= 20 * m^0.05)
    end
    for L in [200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9]
        M = ceil(L)
        lM = log(M)
        ok &= (L / 16)^4 / 24 > L + 1 >= M && 16lM < L
        ok &= M^16 >= 2 && lM >= 1 && M <= 2L
        ρ = L^2 / M^4
        ok &= ρ * (1 + L) <= 2 / M <= 1
        logqR = L + 16lM + log1p(2 * exp(-L - 16lM))
        ok &= logqR <= 18M && 2 + 2π * M^16 <= 8 * M^16
        k = logqR * (2 / M^16 + 2π) / (M^3 * 700 * lM)
        ok &= k * (1 + L) <= 288 / (700M) <= 1
        ok &= 700 <= 700lM <= 1400 * log(L)
    end
    s1 = 0.0
    for t in 2:10^6
        s1 += 1 / (t * log(t))
        if t in (2, 3, 10, 100, 10^3, 10^4, 10^5, 10^6)
            ok &= t >= 3 ? s1 <= 3 + log(log(t)) : s1 <= 3
        end
    end
    ok, worstS
end
okK, worstSK = checkK()
report("K", okK, "prod_(p<=Y) (1-1/p)^-1 <= e^11 log Y for Y <= 10^6 (max ratio $(round(worstSK, sigdigits = 3))); " *
       "sum m^(-19/20) <= 20 M^(1/20); Proposition 5.4 at 8 values of log q")

# (L) Lemmas 6.2 and 6.3
function is_prime_power(n)
    isp(n) && return true
    p = n <= LIMIT ? spf(n) : first(p for p in PRIMES if n % p == 0)
    while n % p == 0
        n ÷= p
    end
    n == 1
end
function checkL()
    ok, cases, worstB, worstN = true, 0, 0.0, 0.0
    for q in PRIMES
        101 <= q <= 401 || continue
        j = 0
        while 2^(j + 1) * q <= XL
            M = 2^j
            cnt = count(m -> is_prime_power(1 + m * q), M:2M-1)
            worstN = max(worstN, cnt / (393M / (j + 1)))
            ok &= cnt <= 393M / (j + 1)
            for z in sort(unique([2, 3, 5, 10, 30, isqrt(q), q - 1]))
                bnd = 2M / log(z) + z * (1 + log(z))^2 + z
                worstB = max(worstB, cnt / bnd)
                ok &= cnt <= bnd
                cases += 1
            end
            j += 1
        end
    end
    for k in 0:200000
        u = 1 + k / 1000
        ok &= (2 + u)^2 * (32u + 1) <= 297u^3 && u^3 <= 2^(3u)
        ok &= (1 + u * log(2))^2 + 1 <= (2 + u)^2
    end
    ok &= all(64 * (j + 1) <= 96j * log(2) for j in 32:10^5-1)
    ok &= 50 * log(2) <= 35 && log(25) <= 4 && log(log(3)) > 1 / 11
    ok &= 40 <= 440 * log(log(3)) && 393 == 96 + 297
    for q in PRIMES[2:end]
        J = floor(Int, 16 * log2(q)) + 1
        ok &= J <= 25 * log(q) && big(2)^J > big(q)^16 && big(2)^J <= 2 * big(q)^16
    end
    ok, cases, worstB, worstN
end
okL, casesL, worstBL, worstNL = checkL()
report("L", okL, "block counts <= sieve bound in $casesL cases (max ratio $(round(worstBL, digits = 4))); " *
       "N_j <= 393 2^j/(j+1) (max ratio $(round(worstNL, digits = 4))); the inequalities of Lemma 6.3 on " *
       "grids and for primes q <= 10^6")

# (M) Theorem 1.3: L'/L(1, chi) = -log q + sum chi(a) gamma_1(a/q) / sum chi(a) psi(a/q)
const B2 = Float64[1 // 6, -1 // 30, 1 // 42, -1 // 30, 5 // 66, -691 // 2730, 7 // 6, -3617 // 510]
const HARM = Float64[sum((1 // i for i in 1:n); init = 0 // 1) for n in 0:19]
const EM_N = 30
const EULER = 0.5772156649015329

function digam(a)
    x = a + EM_N
    s = log(x) - 1 / (2x) - sum(B2[j+1] / ((2j + 2) * x^(2j + 2)) for j in 0:7)
    s - sum(1 / (a + k) for k in 0:EM_N-1)
end
function stieltjes1(a)
    x = a + EM_N
    lx = log(x)
    s = sum(log(a + k) / (a + k) for k in 0:EM_N-1) - lx^2 / 2 + lx / (2x)
    s + sum(B2[j+1] * (lx - HARM[2j+2]) / ((2j + 2) * x^(2j + 2)) for j in 0:7)
end

function primitive_root(q)
    fs = prime_factors(q - 1)
    first(g for g in 2:q-1 if all(powermod(g, (q - 1) ÷ f, q) != 1 for f in fs))
end
function ek(q)
    g = primitive_root(q)
    pw = [powermod(g, k, q) for k in 0:q-2]
    ps = [digam(pw[k+1] / q) for k in 0:q-2]
    g1 = [stieltjes1(pw[k+1] / q) for k in 0:q-2]
    roots = [cis(2π * m / (q - 1)) for m in 0:q-2]
    tot, mx = 0.0im, 0.0
    for j in 1:q-2
        num = sum(roots[(j * k) % (q - 1) + 1] * g1[k+1] for k in 0:q-2)
        den = sum(roots[(j * k) % (q - 1) + 1] * ps[k+1] for k in 0:q-2)
        r = -log(q) + num / den
        tot += r
        mx = max(mx, abs(r))
    end
    EULER + tot, mx
end

# gamma_q from mpmath at 90 digits: euler + sum over chi != 1 of L'/L(1, chi), the logarithmic
# derivative taken from the Hurwitz zeta function and its derivative at s = 1 + 10^-25
const REF = Dict{Int,Float64}(3 => 0.945497280871680703, 5 => 1.72062421251340476,
    7 => 2.08759407471733013, 11 => 2.41542590428326783, 13 => 2.6107577374176502,
    19 => 4.79040941571428333, 101 => 5.29701289150966972, 199 => 6.47366513609320739,
    293 => 3.38438152121953979)
function checkM()
    ok = abs(digam(1.0) + EULER) < 1e-13 && abs(stieltjes1(1.0) + 0.0728158454836767) < 1e-13
    ok &= abs(digam(0.5) + EULER + 2 * log(2)) < 1e-13
    lo, hi, mxr, vals = 1e9, -1e9, 0.0, Dict{Int,Float64}()
    for q in PRIMES
        3 <= q <= 1000 || continue
        gq, mx = ek(q)
        vals[q] = real(gq)
        ok &= abs(imag(gq)) < 1e-9
        lo, hi = min(lo, real(gq) / log(q)), max(hi, real(gq) / log(q))
        mxr = max(mxr, mx / log(log(q)))
    end
    worstR = isempty(REF) ? 0.0 : maximum(abs(vals[q] - v) for (q, v) in REF)
    ok &= worstR < 1e-9
    ok, lo, hi, mxr, vals, worstR
end
okM, lo, hi, mxr, vals, worstR = checkM()
report("M", okM, "gamma_q for primes 3 <= q <= 1000 is real with $(round(lo, digits = 4)) <= gamma_q/log q <= " *
       "$(round(hi, digits = 4)); max |L'/L(1,chi)|/log log q = $(round(mxr, digits = 4)); " *
       "gamma_3 = $(round(vals[3], digits = 12)), gamma_19 = $(round(vals[19], digits = 12)); " *
       "$(length(REF)) values agree with mpmath to $(round(worstR, sigdigits = 2))")

println(fails == 0 ? "ALL PASS" : "$fails FAILED")
exit(fails == 0 ? 0 : 1)
