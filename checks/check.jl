# Numerical checks in Julia for "The Pólya–Vinogradov inequality with log log q".
# (A) G(p) < p for every prime 3 <= p <= 10^7;
# (B) the character identity for every prime p <= 200 and 0 <= n < 3p;
# (E) the exponent arithmetic of Section 4 in exact rationals;
# (G) the unsmoothing identity of Lemma 5.2 in exact rationals;
# (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
# (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6 in exact rationals;
# (J) |tau|^2 = q and Lemma 7.1 for the quadratic characters modulo primes q <= 3000, and the ratio
#     max_x |sum_{n<=x} (n/q)| / (sqrt(q) log log q) for primes 1000 <= q <= 20000;
# (K) the bound |r(theta)| < 3 in the proof of Lemma 7.1 on a grid;
# (L) the parameter inequalities in the proof of Proposition 7.4;
# (M) Lemmas 6.2 and 6.3 (spacing of the multiples of alpha, the bilinear bounds) on random data;
# (N) Lemma 6.4 for characters and random completely multiplicative f;
# (O) Lemma 6.5: the prime pair bound for X <= 10^5 and even 0 < |h| <= 100, the sieve
#     remainders |R_d| <= tau(d), and the fourth moment of G(h) for X <= 10^5;
# (P) the numerical constants and the parameters I, J in the proof of Theorem 6.1.
# Exit status 1 if a check fails.

function primes_upto(n)
    comp = falses(n)
    ps = Int[]
    for i in 2:n
        comp[i] && continue
        push!(ps, i)
        for j in i*i:i:n
            comp[j] = true
        end
    end
    ps
end

function factor_primes(n)
    fs = Int[]
    q = 2
    while q * q <= n
        if n % q == 0
            push!(fs, q)
            while n % q == 0
                n ÷= q
            end
        end
        q += 1
    end
    n > 1 && push!(fs, n)
    fs
end

isprimroot(a, p, fs) = all(q -> powermod(a, (p - 1) ÷ q, p) != 1, fs)

fails = 0
report(name, ok, detail) = (println(ok ? "PASS " : "FAIL ", name, ": ", detail); global fails += !ok)

const LIM = 10^7
ps = primes_upto(LIM)

# (A)
okA, cnt, tot, wg, wp = true, 0, 0, 0, 0
for k in 2:length(ps)
    p = ps[k]
    fs = factor_primes(p - 1)
    g = 0
    for t in 1:k-1
        if isprimroot(ps[t], p, fs)
            g = ps[t]
            break
        end
    end
    if g == 0
        global okA = false
        break
    end
    global cnt += 1
    global tot += g
    if g > wg
        global wg, wp = g, p
    end
end
report("A", okA, "$cnt primes 3..10^7, max G(p) = $wg at p = $wp, sum G(p) = $tot")

# (B)
mobius(d) = (fs = factor_primes(d); prod(fs; init = 1) == d ? (-1)^length(fs) : 0)
okB = true
for p in ps
    p > 200 && break
    N = p - 1
    fs = factor_primes(N)
    g = N == 1 ? 1 : first(a for a in 2:p-1 if isprimroot(a, p, fs))
    lg = Dict(powermod(g, k, p) => k for k in 0:N-1)
    ζ = cis(2π / N)
    for n in 0:3p-1
        r = n % p
        lhs = (r != 0 && gcd(lg[r], N) == 1) ? 1 : 0
        rhs = zero(ComplexF64)
        for d in 1:N
            N % d == 0 || continue
            inner = zero(ComplexF64)
            for m in 0:d-1
                r == 0 && continue
                inner += ζ^mod(lg[r] * m * (N ÷ d), N)
            end
            rhs += mobius(d) / d * inner
        end
        abs(rhs - lhs) > 1e-8 && (global okB = false)
    end
end
report("B", okB, "character identity for primitive roots, p <= 200")

# (E)
okE = true
for η in [1//10^6, 1//1000, 1//7, 1//1, 5//1, 10^6//1]
    ε8 = η / (2000 * (8 + η))
    β = 1//8 - 8 * ε8
    σ = 7//8 + 8 * ε8
    global okE &= (0 < ε8 < 1//1000) && β > 0 && (8 + η) * β >= 1 && σ + β == 1 &&
                  (8 + η) * 8 * ε8 == η / 250
end
report("E", okE, "0 < e < 1/1000, beta > 0, (8+eta) beta >= 1, exact rationals")

# (G)
legendre(n, q) = (r = powermod(mod(n, q), (q - 1) ÷ 2, q); r == 0 ? 0 : (r == 1 ? 1 : -1))
chars = Function[n -> iseven(n) ? 0 : (mod(n, 4) == 1 ? 1 : -1)]
for q in [3, 5, 7, 101, 997]
    push!(chars, n -> legendre(n, q))
end
okG = true
casesG = 0
for χ in chars, x in [1//1, 5//2, 37//3, 1000//1, 12345//7], h in [1//3, 1//1, 7//2, 40//1, 333//4]
    T(y) = sum((χ(n) * (y - n) for n in 1:floor(Int, y)); init = 0//1)
    S = sum((χ(n) for n in 1:floor(Int, x)); init = 0)
    lhs = T(x + h) - T(x) - h * S
    tail = sum((χ(n) * (x + h - n) for n in floor(Int, x)+1:floor(Int, x + h)); init = 0//1)
    global okG &= lhs == tail && abs(lhs) <= h * (h + 1)
    global casesG += 1
end
report("G", okG, "unsmoothing identity and |tail| <= h(h+1), $casesG cases, exact")

# (H)
st = UInt64(12345)
function rnd()
    global st = st * 0x5851f42d4c957f2d + 0x14057b7ef767814f
    (st >> 11) / 2.0^53
end
okH = true
worstH = 0.0
for _ in 1:200000
    x = 1 + 1e6 * rnd(); h = x * rnd(); σ = 0.5 + 1.5 * rnd(); t = -100 + 200 * rnd()
    w = complex(σ + 1, t)
    d = abs(exp(w * log(x + h)) - exp(w * log(x)))
    b = min(abs(w) * h * (x + h)^σ, 2 * (x + h)^(σ + 1))
    global worstH = max(worstH, d / b)
    global okH &= d <= b * (1 + 1e-9)
    s0 = 0.5 + 0.5 * rnd(); ee = 0.125 * (1 - rnd()); hh = x^s0
    global okH &= (x + hh)^s0 <= 2 * hh * (1 + 1e-12) && (3 * hh)^(1 - 4 * ee) <= 3 * hh * (1 + 1e-12) &&
                  (2 * (x + hh))^(4 * ee) <= 4 * x^(4 * ee) * (1 + 1e-12)
end
report("H", okH, "kernel and size bounds at 200000 random points, max ratio $(round(worstH; digits = 6))")

# (I)
okI = true
for δ in [1//10^6, 1//1000, 1//7, 1//1, 5//1, 1000//1]
    f1 = min(δ / 8, 1//2000); a1 = 7//8 - 2 * f1
    global okI &= 0 < f1 < 1//1000 && 8 * f1 <= δ && 1//2 <= a1 <= 1 && a1 + 2 * f1 == 7//8 && a1 + 8 * f1 <= 7//8 + δ
    d = min(δ, 1//1); f = min(d / 12, 1//2000); ε = d / 8; a = 7//8 - 2 * f
    global okI &= 0 < f < 1//1000 && 0 < ε <= 1//8 && 1//2 <= a && a + 8 * f <= 1 &&
                  a + 8 * f + 4 * ε <= 7//8 + δ && a + 2 * f == 7//8
end
for (η, θ) in [(1//1000, 7//8 + 1//10^6), (1//1, 9//10), (1000//1, 1//1), (1//7, 15//16)]
    dc = (θ - 7//8) * η / (1 + η)
    global okI &= dc > 0 && dc / η + 7//8 + dc == θ
end
report("I", okI, "parameters of Theorems 1.4, 1.5 and Corollary 1.6, exact rationals")

# (J)
function quadtable(q)
    tab = fill(-1, q); tab[1] = 0
    for a in 1:q-1
        tab[(a * a) % q + 1] = 1
    end
    tab
end
ispJ = trues(20000); ispJ[1] = false
for i in 2:141, j in i*i:i:20000
    ispJ[j] = false
end
okJ = true; worstτ = 0.0; nJ = 0; worstJ = 0.0
for q in 3:20000
    ispJ[q] || continue
    tab = quadtable(q)
    run = 0; m = 0
    for n in 1:q-1
        run += tab[n+1]; m = max(m, abs(run))
    end
    if q <= 3000
        τ = sum(tab[a+1] * cispi(2a / q) for a in 1:q-1)
        global worstτ = max(worstτ, abs(abs2(τ) - q) / q)
        b0 = sum(1 / k for k in 1:q÷2)
        global okJ &= m <= sqrt(q) * (b0 + 6)
        global nJ += 1
    end
    q >= 1000 && (global worstJ = max(worstJ, m / (sqrt(q) * log(log(q)))))
end
okJ &= worstτ < 1e-9 && worstJ < 2
report("J", okJ, "|tau|^2 = q (max rel. error $(round(worstτ; sigdigits = 2))) and max|S| <= sqrt(q)(B+6) for $nJ primes; max ratio for 1000 <= q <= 20000: $(round(worstJ; digits = 4))")

# (K)
worstK = 0.0
for k in 1:500000, th in (k / 1e6, -k / 1e6)
    r = 1 / (1 - cispi(-2th)) - 1 / (2im * pi * th)
    global worstK = max(worstK, abs(r))
end
report("K", worstK < 3, "|r(theta)| on 10^6 grid points of 0 < |theta| <= 1/2, max $(round(worstK; digits = 6))")

# (L) Proposition 7.4: M = ceil(L), R = M^16, Y = M^700
function checkL()
    ok = true
    for L in [200.0, 200.5, 201.0, 250.0, 1000.0, 1e4, 1e6, 1e9]
        M = ceil(L); lM = log(M)
        ok &= (L / 16)^4 / 24 > L + 1 >= M && 16lM < L && M^16 >= 2 && lM >= 1 && M <= 2L
        ρ = L^2 / M^4
        ok &= ρ * (1 + L) <= 2 / M <= 128
        logqR = L + 16lM + log1p(2exp(-L - 16lM))
        ok &= logqR <= 18M && 2 + 2pi * M^16 <= 8M^16
        k = logqR * (2 / M^16 + 2pi) / (M^3 * 700 * lM)
        ok &= k * (1 + L) <= 288 / (700M) <= 1 && 700lM <= 1400log(L)
    end
    s1 = 0.0
    for t in 2:10^6
        s1 += 1 / (t * log(t))
        t in (2, 3, 10, 100, 10^3, 10^4, 10^5, 10^6) && (ok &= t >= 3 ? s1 <= 3 + log(log(t)) : s1 <= 3)
    end
    ok
end
report("L", checkL(), "parameter inequalities of Proposition 7.4 at 8 values of log q; sum_{2<=t<=H} 1/(t log t) <= 3 + log log H for H <= 10^6")

# (M) Lemma 6.2 (spacing) and Lemma 6.3 (bilinear bounds) on random data
dist(x) = abs(x - round(x))
wM(M, θ) = (d = dist(θ); d < 1 / M ? M : 1 / d)
function checkM()
    ok = true
    for _ in 1:3000
        r = 2 + floor(Int, 400rnd())
        a = floor(Int, r * rnd())
        while gcd(a, r) != 1
            a = mod(a + 1, r)
        end
        α = a / r + (2rnd() - 1) / r^2 + floor(Int, 20rnd()) - 10
        for k in 1:r÷2
            ok &= dist(k * α) >= 1 / (2r) - 1e-12
        end
        H = floor(Int, 1000rnd())
        ds = [dist(h * α) for h in 1:H]
        for _ in 1:3
            t = 0.5rnd()
            ok &= count(<(t), ds) <= (4H / r + 1) * (4r * t + 1)
        end
        M = 0.5 + 1000rnd()
        K = max(0, ceil(Int, log2(M)))
        ws = [d < 1 / M ? M : 1 / d for d in ds]
        ok &= sum(ws; init = 0.0) <= (4H / r + 1) * (3M + 4r + 8r * K)
        ok &= sum(abs2, ws; init = 0.0) <= (4H / r + 1) * (20r * M + 3M^2)
    end
    for _ in 1:2000
        θ = 2rnd() - 1; U = 0.5 + 300rnd(); A = floor(Int, 1000rnd()); B = A + floor(Int, U * rnd())
        S = sum((cispi(2x * θ) for x in A+1:B); init = 0.0im)
        ok &= abs(S) <= wM(U, θ) * (1 + 1e-9)
    end
    for _ in 1:300
        α = rnd(); U = 1 + 50rnd(); A = floor(Int, 100rnd()); B = A + floor(Int, U); N = floor(Int, 2000rnd()) + 1
        V = sort(unique([1 + floor(Int, 60rnd()) for _ in 1:1+floor(Int, 20rnd())]))
        b = Dict(v => cispi(2rnd()) * rnd() for v in V)
        lhs = sum(abs2(sum((b[v] * cispi(2u * v * α) for v in V if u * v <= N); init = 0.0im)) for u in A+1:B)
        rhs = sum(abs(b[v]) * abs(b[w]) * wM(U, (v - w) * α) for v in V, w in V)
        ok &= lhs <= rhs * (1 + 1e-9) + 1e-9
        Hh = floor(Int, 80rnd()); Mm = 0.5 + 100rnd()
        lhs2 = sum((wM(Mm, (m - m2) * α) for m in 1:Hh, m2 in 1:Hh); init = 0.0)
        ok &= lhs2 <= Hh * (Mm + 2sum((wM(Mm, h * α) for h in 1:Hh); init = 0.0)) * (1 + 1e-12)
    end
    ok
end
report("M", checkM(), "Lemma 6.2 (i)-(iii) for 3000 random (alpha, a/r), Lemma 6.3 (i) at 2000 and (ii), (iii) at 300 random cases")

# (N) Lemma 6.4
const ζ32 = 2.612375348685488
const C5 = 1 + 4ζ32
function spf_upto(n)
    spf = collect(0:n)
    for i in 2:isqrt(n), j in i*i:i:n
        spf[j+1] == j && (spf[j+1] = i)
    end
    spf
end
function checkN()
    ok = true; worst = 0.0
    spf = spf_upto(3000)
    for trial in 0:59
        N = 2 + floor(Int, 2998rnd()); α = rnd()
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
                p = spf[n+1]
                haskey(fp, p) || (fp[p] = cispi(2rnd()) * (trial % 3 == 2 ? rnd() : 1.0))
                f[n] = fp[p] * f[n÷p]
            end
        end
        S = sum(f[n] * cispi(2n * α) for n in 1:N)
        T = 0.0im
        for p in 2:N
            spf[p+1] == p || continue
            T += log(p) * f[p] * sum(f[m] * cispi(2p * m * α) for m in 1:N÷p)
        end
        err = abs(S * log(N) - T) / N
        worst = max(worst, err)
        ok &= err <= C5
    end
    ok, worst
end
okN, worstN = checkN()
report("N", okN, "Lemma 6.4 for 60 completely multiplicative f, N <= 3000: max error / N = $(round(worstN; digits = 4)) <= C5 = $(round(C5; digits = 4))")

# (O) Lemma 6.5
Gof(h, spf) = (g = 1.0; n = abs(h); while n > 1; p = spf[n+1]; g *= p / (p - 1); while n % p == 0; n ÷= p; end; end; g)
function checkO()
    XO = 10^5
    spf = spf_upto(XO + 200)
    isp(n) = n >= 2 && spf[n+1] == n
    ok = true; worst = 0.0
    for h in [2:2:100; -100:2:-2]
        g2 = Gof(h, spf)^2
        bound(X) = 400g2 * X / log(X)^2 + 3X^0.6
        cnt = 0
        for X in 2:XO
            n = X - 1
            jump = n + h >= 0 && isp(n) && isp(n + h)
            jump && (cnt += 1)
            if jump || X <= 8
                ok &= cnt <= bound(X)
                worst = max(worst, cnt / bound(X))
            end
        end
    end
    for X in [1, 2, 7, 100, 1001, 2000], h in [2, 6, 30, 98, -4], d in [1, 3, 5, 7, 15, 21, 35, 105, 11, 143, 1155]
        gcd(d, h) == 1 || continue
        τ = 2^count(p -> d % p == 0, [3, 5, 7, 11, 13])
        c = count(n -> mod(n * (n + h), d) == 0, 0:X-1)
        ok &= abs(c - τ * X / d) <= τ
    end
    for X in [collect(2:10^5 - 1); [big(10)^k for k in 6:39]]
        m = Int(round(Float64(X)^0.1)) + 2
        while big(m)^10 > X
            m -= 1
        end
        ok &= big(isqrt(m) + 1)^20 > X
    end
    acc = 0.0; worstG = 0.0
    for h in 1:XO
        acc += Gof(h, spf)^4
        worstG = max(worstG, acc / h)
    end
    ok &= worstG <= exp(30) && all(t -> big(t + 1)^5 <= big(t + 31) * big(t)^4, 1:10^5 - 1) && pi^2 / 6 - 1 <= 1
    ok, worst, worstG
end
okO, worstO, worstGO = checkO()
report("O", okO, "prime pairs: count <= 400 G(h)^2 X/log^2 X + 3 X^(3/5) for X <= 10^5, 0 < |h| <= 100 even (max ratio $(round(worstO; digits = 4))); |R_d| <= tau(d); (T+1)^20 > X; max_X X^-1 sum G(h)^4 = $(round(worstGO; digits = 3)) <= e^30")

# (P) constants and parameters in the proof of Theorem 6.1
function checkP()
    ok = 64log(2) < 45
    for ℓ in 64:10^4
        I = ndigits(ℓ; base = 2); J = ℓ + 1 - 4I
        L = big(ℓ)
        ok &= big(16)^I > L^4 && 1 <= J <= ℓ && 4I <= ℓ && 2^I <= 2ℓ && big(2)^J * big(16)^I == big(2)^(ℓ + 1)
        ok &= big(J)^2 * big(2)^J * L^4 <= (L + 1)^2 * big(2)^(ℓ + 1) && (L + 1)^2 <= L^4
    end
    ok &= log(2) >= 0.5 && (7//4) / (1//4)^3 == 112
    tail = sum(big(j + 1)^2 * big(3)^j // big(4)^j for j in 0:399)
    ok &= 111.99 < tail <= 112
    ok &= all(j -> (1 + 2big(j)) * big(8)^j <= 2 * big(j + 1)^2 * big(9)^j, 0:1999)
    ok &= all(J -> sum(2.0^(j / 2) for j in 0:J-1) <= 3 * 2.0^(J / 2), 1:199)
    ok &= 3sqrt(14) <= 12 && sqrt(24) <= 5 && 8 * 112 + 12 == 908 && 6 * 225 == 1350 <= 37^2 && 15 + 37 == 52
    ok &= all(c -> c <= 40^4, [320 * 15^3, 48 * 15^4, 80 * 15^3, 180 * 15^3]) && 2^0.25 <= 2 && 2^0.3 <= 2
    ok &= 2 + 16 + 32 * 2 * 15^3 == 216018
    xs = [1 + 10^(k / 10) for k in 0:2999]
    ok &= all(x -> log(x) <= 15x^(1 / 15) && log(x) <= 4x^0.25, xs)
    ok &= all(N -> N * log(N) - sum(log, 1:N; init = 0.0) <= N, 1:10^4)
    ps = primes_upto(10^6)
    ok &= sum(log(p) / (p * (p - 1)) for p in ps) <= 2sum(log(p) / p^2 for p in ps) <= 2ζ32
    Kb = 80sqrt(800exp(15)) + 52
    ok, Kb, 45 + C5 + 908 + 216018Kb + 60 + 2Kb
end
okP, Kb, C1 = checkP()
report("P", okP, "constants of Theorem 6.1: coefficients <= 40^4, 896 = 8*112, I, J for 64 <= ell <= 10^4; K_b = $(round(Kb; sigdigits = 5)), C_1 = $(round(C1; sigdigits = 5))")

println(fails == 0 ? "ALL PASS" : "$fails FAILED")
exit(fails == 0 ? 0 : 1)
