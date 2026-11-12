# For each prime 5 <= q <= QMAX: the character chi_j (least primitive root g) with the largest M(chi),
# its parity, the smallest x where |S(x)| = M(chi), M/sqrt(q) and M/(sqrt(q) log log q).
using Printf
isprime(n) = n >= 2 && all(n % d != 0 for d in 2:isqrt(n))
function primroot(q)
    f = [p for p in 2:q-1 if (q-1) % p == 0 && isprime(p)]
    for g in 2:q-1
        all(powermod(g, (q-1) ÷ p, q) != 1 for p in f) && return g
    end
end
function main(QMAX)
    for q in 5:QMAX
        isprime(q) || continue
        g = primroot(q); ind = zeros(Int, q); r = 1
        for k in 0:q-2; ind[r+1] = k; r = r*g % q; end
        bj = 0; bx = 0; bm = 0.0
        for j in 1:q-2
            s = 0.0 + 0.0im
            for n in 1:q-1
                s += cispi(2 * ((j * ind[n+1]) % (q-1)) / (q-1))
                if abs(s) > bm + 1e-9; bm = abs(s); bj = j; bx = n; end
            end
        end
        @printf("%d %d %d %s %d %.4f %.4f\n", q, g, bj, isodd(bj) ? "odd" : "even", bx, bm/sqrt(q), bm/(sqrt(q)*log(log(q))))
    end
end
main(parse(Int, ARGS[1]))
