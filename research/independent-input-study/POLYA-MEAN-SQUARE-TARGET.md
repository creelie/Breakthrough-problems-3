# An independent analytic target and a tested obstruction to a shortcut

25 October 2026. Research supplement to Paper 6. The mean-square input below
is **not proved**. No independent zero-free theorem is claimed.

## Conditional extraction lemma

Fix 1<=alpha<6/5. Suppose an average of nonnegative squared row sums satisfies

    sum_rows |A_u(D)|^2 <= C_epsilon D^(1+epsilon) H,
    H comparable to D^alpha,

for every epsilon>0 and every fixed smooth weight. Suppose at least
c H^(1/6)/log(H) distinct rows satisfy

    |A_u(D)-S(D)| <= C D H^(-1/6).

Then, for every epsilon>0,

    |S(D)| <= C'_epsilon D^(1/2+5alpha/12+epsilon).

Proof: write R for the number of those rows and E for their error bound.
The reverse triangle inequality gives

    R max(|S(D)|-E,0)^2 <= sum_rows |A_u(D)|^2.

Thus |S(D)|<=E+(C_epsilon D^(1+epsilon) H/R)^(1/2).
Substitute the lower bound on R and H comparable to D^alpha. The two powers
are 1-alpha/6 and 1/2+5alpha/12, up to an arbitrarily small error. For alpha>=1,
the second is larger. Absorb the square root of log(H) into D^epsilon.
This proves the implication without asserting either of its hypotheses.

In particular, alpha=21/20 gives main exponent 15/16 and error exponent
33/40. The exact arithmetic and the strict threshold alpha<6/5 are checked
by mean_square_controls.py. These checks establish algebraic parameter
relations, not the analytic mean-square estimate.

## A possible arithmetic realization, still an unproved input

Let K=Q(sqrt(-3)). For every fixed finite-order Hecke character nu, form
smooth sums with coefficients mu_K(n)nu(n), away from the primes over 6,
and twist them by sextic residue symbols (u/n)_6. Rows u=pi^6, with pi a
prime element of norm comparable to H^(1/6), have (pi^6/n)_6=1 unless pi|n.
Their missing terms are bounded by O(D/H^(1/6)); there are
at least c H^(1/6)/log H such distinct rows for large H, with the fixed
bad primes removed. The counting assertion is a classical prime-ideal
counting consequence; it does not require a fixed zero-free half-plane.

If the displayed mean-square estimate could be proved independently for
these ACTUAL Mobius coefficients at H comparable to D^(21/20), for every
fixed nu and weight, the extraction lemma would yield

    sum_n mu_K(n)nu(n)W(N(n)/D) = O_nu,W,epsilon(D^(15/16+epsilon)).

Mellin inversion, with a weight nonzero at a hypothetical zero, would
exclude zeros of L_K(s,nu) in Re(s)>15/16. Finite omitted Euler factors
have no zeros or poles in Re(s)>0. The usual quadratic base-change
factorization would then give the corresponding Dirichlet nonvanishing,
with the point s=1 handled by classical nonvanishing there. Appendix B
of the existing manuscript transfers any such fixed boundary below one
to the desired character-sum bound.

This is a sufficient research target, not a new proof of its mean-square
hypothesis. The sixth-power extraction is part of the existing OpenAI
method and is credited, not claimed as a new discovery. The published
quadratic large sieve and cubic-theta inputs do not, by citation alone,
establish the specialized Mobius estimate in the stated range.

Background sources consulted: OpenAI, *The Quasi-Riemann Hypothesis*,
5 October 2026 (the existing credited local manuscript);
Michael Rubinstein's explicitly provisional reading notes,
https://www.math.uwaterloo.ca/~mrubinst/quasi_rh_notes/ . The latter's
guide explicitly retains an unproved transfer estimate from the source
paper; it is not treated as an independent proof of that estimate.

## Why an arbitrary-coefficient large-sieve replacement fails

A tempting shortcut would assert the same DH bound for arbitrary coefficients
of modulus at most one. That stronger assertion is false in this range.

Choose the columns to be primes p in [D,2D] with p=1 modulo 6, and choose
an order-six character rho_p modulo each p. Put coefficient 1 on each of
these columns and zero elsewhere. For every integer a with
1<=a<=H^(1/6), and large D with H comparable to D^alpha, alpha<6/5,
one has a<p and

    rho_p(a^6)=1.

There are floor(H^(1/6)) such rows. If C_D denotes the number of columns,
the squared-row average is at least floor(H^(1/6)) C_D^2. The classical
prime number theorem in this fixed progression gives C_D comparable to
D/log D. A bound O_epsilon(D^(1+epsilon)H) would therefore require

    D^(2+alpha/6)/(log D)^2 <= constant D^(1+alpha+epsilon),

which fails for epsilon<1-5alpha/6. The exponent on the right can thus
not be obtained for arbitrary coefficients in precisely the range needed
by the extraction lemma. This is not a counterexample to the estimate
for the full Mobius coefficients: the selected prime-only column weights
are different coefficients.

The same issue prevents restricting rows to squarefree indices and simply
applying a quadratic large sieve: the sixth-power rows used to recover S(D)
would have been removed. A proof must handle their contribution while using
the arithmetic cancellation of the actual coefficients.

## Remaining obligation

No independent proof of the specialized mean-square estimate was found.
The existing closed Mobius endpoints still invoke the credited OpenAI
nonvanishing theorem. Applying their converse to those same endpoints is
circular as an independent proof. The supplemental parameter checks and
residue-symbol identities do not verify an estimate for every D, nu and weight.

This supplement records a weaker sufficient analytic target and a rigorous
obstruction to an overly strong replacement. It is not an unconditional
no-dependency proof of the optimal Polya-Vinogradov inequality.
