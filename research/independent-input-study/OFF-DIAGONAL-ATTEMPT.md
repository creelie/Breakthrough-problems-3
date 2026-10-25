# Expanding the missing mean-square estimate

25 October 2026. Exact identities and bounds below do not prove the needed
short-row mean-square estimate.

Let a_n=mu_K(n)nu(n)W(N(n)/D), supported on the indicated norm shell, and
let chi_n(u) be the sextic residue character. For any finite set of rows U,

    M = sum_(u in U) |sum_n a_n chi_n(u)|^2
      = sum_(n,m) a_n conjugate(a_m) K_U(n,m),
    K_U(n,m)=sum_(u in U) chi_n(u) conjugate(chi_m(u)).

This follows by expanding finite products; no convergence or zero-free input
is involved. Since |chi_n(u)|<=1, the diagonal is at most

    |U| sum_n |a_n|^2 = O_W(H D)

when |U|=O(H) and the norm shell contains O(D) ideals. The sought bound
therefore requires control of the TOTAL signed off-diagonal sum. Replacing
its summands by their absolute values gives only O_W(H D^2).

Even a generic large-sieve estimate of the schematic shape

    M <= constant D (H+D^2)

would not finish the construction. At H=D^(21/20), its D^3 term, divided
by the D^(7/40) repeated-row count and then square-rooted, gives exponent
113/80>1. This calculation does not assert that a particular large-sieve
theorem applies to every convention of the present Hecke family; it shows
that even that schematic generic bound would be insufficient.

The independent finite-sum derivation in GAUSS-JACOBI-CONSTRUCTION.md gives
an exact encoding mu_K(n)=G(n)^3/(N(n)n) for the stated squarefree prime
generators. It closes that arithmetic identity. However, the numerator and
denominator have the same absolute value. Taking norms immediately returns
|mu_K(n)|=1 and loses the phase information. A bound for the off-diagonal
phase correlations is still required. No inequality supplying that saving
was derived here.

There is a complete orthogonality identity over a full common residue period:
for distinct multiplicative characters eta_j of a finite unit group G,

    sum_(u in G) |sum_j b_j eta_j(u)|^2 = |G| sum_j |b_j|^2.

Its proof is the elementary character orthogonality relation. For a growing
family of conductors, the common residue modulus can be a product of all
those conductors. This identity does not control the much shorter row
range H=D^(21/20). Replacing that short range by a full enormous period
changes the extraction bound and does not give the needed power saving.

Thus the diagonal and the arithmetic encoding have complete proofs. The
required short-range, coefficient-specific off-diagonal estimate remains
the missing step. Neither the complete-period identity nor the exact
Gauss/Jacobi tests is reported as proving that step.
