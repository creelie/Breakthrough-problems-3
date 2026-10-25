# Meaning of source completeness and independence

The package includes the credited zero-free proof sources and their nonstandard
import closure. The closed endpoints do not state nonvanishing as a hypothesis.
Their proof invokes a supplied theorem whose own proof is compiled from source
and whose axiom closure is inspected. That removes the need to trust an
unproved assertion in an external preprint PDF.

It does not remove the mathematical contribution of OpenAI or create a new
independent proof by the manuscript authors. No such independent proof has
been found. Original author names, Apache 2.0 notices and source pins remain.
The standard Lean toolchain and Mathlib libraries are pinned dependencies,
not bundled offline installations.

Appendix C's general equivalence, reciprocal estimate, Mellin inversion,
decay, contour argument and finite-sum identity now have Lean sources.
For a fixed nonprincipal character and 0<theta<1, nonvanishing on Re(s)>theta
is equivalent to all compact smooth Möbius bounds O(X^(theta+epsilon)).
The credited 7/8 result supplies the closed estimates X^(7/8+epsilon) and
C_W q^104 X^(11/12). A0=1+(3/2) sum_p p^(-3/2), disc radii 53/48 and 52/48,
and Borel–Carathéodory give exp(105 A0)(7q(1+|t|))^104 for the reciprocal.

Using this consequence to establish the same nonvanishing via the converse
would be circular as a purported independent proof. Numerical computations
cannot replace the estimate for every character, height and scale. Rebuilding
a credited proof checks that proof; it does not change its authorship.
See PROOF-COVERAGE.md for the distinction between locally checked modules,
the current closed endpoint audit and the separate written exposition.
