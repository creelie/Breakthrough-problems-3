# Numerical checks in Julia for "Prime primitive roots below every power of p".
# (A) G(p) < p for every prime 3 <= p <= 10^7;
# (B) the character identity for every prime p <= 200 and 0 <= n < 3p;
# (E) the exponent arithmetic of Section 4 in exact rationals.
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

println(fails == 0 ? "ALL PASS" : "$fails FAILED")
exit(fails == 0 ? 0 : 1)
