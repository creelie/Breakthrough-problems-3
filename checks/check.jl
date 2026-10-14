# Numerical checks in Julia for "Vinogradov's conjectures on primitive roots and character sums".
# (A) G(p) < p for every prime 3 <= p <= 10^7;
# (B) the character identity for every prime p <= 200 and 0 <= n < 3p;
# (E) the exponent arithmetic of Section 4 in exact rationals;
# (G) the unsmoothing identity of Lemma 5.2 in exact rationals;
# (H) the kernel and size bounds in the proof of Proposition 5.3 at random points;
# (I) the parameters of Theorems 1.4, 1.5 and Corollary 1.6 in exact rationals.
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

println(fails == 0 ? "ALL PASS" : "$fails FAILED")
exit(fails == 0 ? 0 : 1)
