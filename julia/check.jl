# Independent recomputation of M(chi) for prime moduli 5 <= q <= QMAX (default 1999; the paper uses 9999) and comparison with the C output,
# plus the numerical inequalities of Lemma 2.6 (Gamma bound) and the constants e^gamma/pi, e^gamma/(sqrt3 pi).
using SpecialFunctions, Printf
isprime(n) = n >= 2 && all(n % d != 0 for d in 2:isqrt(n))
function primroot(q)
    f = [p for p in 2:q-1 if (q-1) % p == 0 && isprime(p)]
    for g in 2:q-1
        all(powermod(g, (q-1) ÷ p, q) != 1 for p in f) && return g
    end
end
# C results: q best M/sqrt(q)  (file mall.txt, column 2)
cres = Dict{Int,Float64}()
for l in eachline(ARGS[1])
    w = split(l); cres[parse(Int, w[1])] = parse(Float64, w[2])
end
function run(cres, QMAX)
fails = 0; nq = 0; nchar = 0
for q in 5:QMAX
    isprime(q) || continue
    g = primroot(q); ind = zeros(Int, q); r = 1
    for k in 0:q-2; ind[r+1] = k; r = r*g % q; end
    best = 0.0
    for j in 1:q-2
        s = 0.0 + 0.0im; m = 0.0
        for n in 1:q-1
            s += cispi(2 * ((j * ind[n+1]) % (q-1)) / (q-1)); m = max(m, abs(s))
        end
        best = max(best, m / sqrt(q)); nchar += 1
    end
    nq += 1
    if abs(best - cres[q]) > 5e-6
        fails += 1; @printf("MISMATCH q=%d julia=%.6f C=%.6f\n", q, best, cres[q])
    end
end
return nq, nchar, fails
end
nq, nchar, fails = run(cres, length(ARGS) > 1 ? parse(Int, ARGS[2]) : 1999)
@printf("moduli %d, characters %d, mismatches %d\n", nq, nchar, fails)
# Gamma bound |Gamma(u+it)| <= 15/(1+t^2) on [3/4,2] x [0,40] (beyond 40 Stirling decay is far smaller)
function gw()
 worst = 0.0
 for u in 0.75:0.005:2.0, t in 0:0.01:40
  worst = max(worst, abs(gamma(u + t*im)) * (1 + t^2) / 15)
 end
 worst
end
worst = gw()
@printf("max |Gamma|(1+t^2)/15 on grid = %.4f (must be < 1)\n", worst)
@printf("e^gamma/pi = %.6f, e^gamma/(sqrt3 pi) = %.6f\n", exp(Base.MathConstants.eulergamma)/pi, exp(Base.MathConstants.eulergamma)/(sqrt(3)*pi))
