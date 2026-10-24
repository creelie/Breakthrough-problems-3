# Möbius estimate and independent-proof status

Appendix C now gives complete written analytic proofs of the following.

For fixed nonprincipal chi and 0 < theta < 1, nonvanishing of L(s,chi) on
Re(s)>theta is equivalent to the estimate

    |sum_n mu(n) chi(n) W(n/X)| <= C(chi,W,epsilon) X^(theta+epsilon)

for every epsilon>0, every complex smooth W compactly supported in (1,2), and
all X>=1. Constants may depend on the fixed character and weight.

Forward: bounded character partial sums give polynomial growth of L; a positive
harmonic logarithm and Harnack's inequality give polynomial growth of 1/L on
each smaller closed half-strip. Rapid Mellin decay then justifies a contour
shift. All boundaries and convergence justifications are written in the article.

Reverse: integrate the smoothed sum against X^(-s-1). The assumed bound gives a
holomorphic function F_W on Re(s)>theta and L F_W = Mellin(W). At a hypothetical
zero rho choose W(y)=y^(-rho) phi(y), with nonzero nonnegative smooth phi inside
(1,2). Then Mellin(W)(rho)=integral phi(y)/y > 0, a contradiction.

Using OpenAI's credited 7/8 theorem, the forward implication proves the estimate
with exponent 7/8+epsilon. Choosing the line 11/12 gives the explicit bound
C_W q^104 X^(11/12), uniformly over nonprincipal characters modulo q.
The disc radii are 53/48 and 52/48, the Harnack ratio is 105, and the reciprocal
growth power is 104. The 107th Mellin decay bound makes the final integral
absolutely convergent. This is a mathematical consequence of the external
theorem, not an independent replacement for it.

No independent proof of the zero-free theorem, or of the equivalent Möbius
estimate without it, has been obtained here. In particular, applying the reverse
implication after the forward implication would be circular as a purported
removal of that input. A successful Lean rebuild of the cited proof would verify
that formal proof, not invent a distinct one. The new Appendix C is not claimed
to be formalised in Lean.

The earlier Burgess-shaped substitution gives no nontrivial saving at the
required polylogarithmic lengths. A bound uniform over arbitrary coefficients
cannot replace the special Möbius mean square: coherent sixth-power rows can
align the prime columns. These failures do not refute the special theorem.
Python, Julia, C, C++ and finite search do not supply the missing universal
analytic argument. The article uses the precise cited-theorem fallback which
the author authorised.
