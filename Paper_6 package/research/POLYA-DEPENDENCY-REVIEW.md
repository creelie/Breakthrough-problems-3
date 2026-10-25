# Pólya–Vinogradov: source completeness and the remaining independence request

25 October 2026. This is a proof-dependency review, not a new zero-free proof.

## What was checked in this pass

The supplied manuscript remains the 29-page article in Paper 6, with its
original coauthors Deep Bhattacharjee and Ushashi Bhattacharya. The article
uses the credited OpenAI nonvanishing theorem. No external article has been
appended to it and no attribution has been removed.

A fresh static import trace from Vinogradov.PV.Main reaches
OAI.NumberTheory.DirichletL.Nonvanishing through

    PV.Main -> PV.Polya -> PV.Gauss -> PV.Smooth -> PV.NonSmooth
    -> PV.Twist -> PV.PrimeSum -> CharacterSums -> Final
    -> OAI.NumberTheory.DirichletL.Nonvanishing.

This trace is one module-import path, not a theorem-level minimal dependency
proof. The transitive nonstandard module closure has 2,973 files, including
2,924 OAI files. All match the audited repository sources after CRLF-to-LF
normalization. The raw delivery digests and normalized digests are recorded.

The Lean source tree is 9914e7a2b60b10d441513e64eacc0856025c9eec.
The seven receipt-file digests were rechecked. The 19 original, seven endpoint
and 20 analytic component axiom reports were parsed again; the only axioms
reported are propext, Classical.choice and Quot.sound. Six negative controls
for the report gate passed. The previous successful full and component CI
runs were confirmed through read-only GitHub requests:

* https://github.com/creelie/Breakthrough-problems-3/actions/runs/40145560153
* https://github.com/creelie/Breakthrough-problems-3/actions/runs/40139438840

These are checks of existing source and completed audits. No new full Lean
compilation was performed in this pass. A kernel check does not by itself
establish novelty, journal acceptance or a translation of every written line.

## A precise sufficient replacement, with a proof of its consequence

One possible independent replacement would be to establish, without invoking
the credited zero-free theorem, the following estimate for every smooth
complex weight W supported in (1,2), every nonprincipal Dirichlet character
chi modulo q, and every X>=1:

    |sum_n mu(n) chi(n) W(n/X)| <= C_W q^104 X^(11/12),

with C_W independent of q, chi and X. This is a sufficient replacement, not
a claim that this particular estimate is necessary for every possible proof
of the optimal Pólya–Vinogradov bound.

To see what the estimate would prove, fix chi and write M_W(X) for the sum.
For Re(s)>1, absolute convergence and u=n/X give

    integral_0^infinity M_W(X) X^(-s-1) dX = W_hat(s)/L(s,chi),
    W_hat(s) = integral_0^infinity W(u) u^(s-1) du.

The integral over 0<X<1 is entire: only n=1 can contribute, and X is
restricted to (1/2,1). The proposed bound makes the remaining integral
holomorphic in Re(s)>11/12, by locally uniform absolute convergence.

If L(rho,chi)=0 in that half-plane, choose a nonzero nonnegative smooth
bump psi supported in (1,2) and put W(u)=u^(-i Im(rho)) psi(u). Then

    W_hat(rho) = integral_1^2 psi(u) u^(Re(rho)-1) du > 0.

Thus W_hat(s)/L(s,chi) has a pole at rho, contradicting the holomorphic
continuation supplied by the integral. Consequently the proposed estimate
would give nonvanishing for Re(s)>11/12. The existing manuscript supplies
the subsequent transfer to the character-sum bound. The Mellin implication
and its more general equivalence are already in Appendix C and its formal
sources; this review does not claim them as new discoveries.

## Why the existing Möbius estimate does not replace the dependency

Vinogradov/Mobius/Complete.lean invokes
OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re in both
smoothed_mobius_bound and smoothed_mobius_cancellation. It first obtains
nonvanishing and then the Möbius estimate. Feeding that estimate into the
converse above returns a consequence of the same input. It is not an
independent proof of the input.

Character periodicity alone bounds sums of chi(n), not sums of mu(n)chi(n).
Likewise, the Euler product proves reciprocal bounds absolutely in Re(s)>1;
moving those bounds left by choosing a holomorphic logarithm already
requires the nonvanishing one is trying to prove. Neither observation
supplies the independent estimate in the displayed range.

## Current disposition

The accompanying formal-proof-sources.zip supplies all nonstandard proof
sources with their existing LICENSE, NOTICE, source pins and build files.
The standard Lean toolchain and pinned Mathlib dependencies still have to
be installed/fetched. This removes the need to obtain a theorem's proof from
an external preprint PDF when checking the formal sources. It does not
remove OpenAI's mathematical contribution, make the argument independently
discovered, or make the source preprint peer reviewed.

No independent replacement estimate or zero-free proof was obtained in
this pass. The original accurate manuscript and its existing DOI are retained.
A new no-dependency or full-closure release is not certified by these files.
