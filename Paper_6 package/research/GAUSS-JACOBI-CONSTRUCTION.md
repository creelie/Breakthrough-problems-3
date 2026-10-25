# A complete arithmetic construction of the Möbius sign

25 October 2026. A self-contained derivation of a classical identity, with
exact finite-field controls. No novelty claim and no analytic mean-square
estimate are asserted.

Let F be a finite field of order q with 3 dividing q-1. Let chi be a
nontrivial cubic multiplicative character, extended by chi(0)=0, and let
psi be a nontrivial additive character. Write omega=exp(2 pi i/3) and

    G(chi)=sum_x chi(x)psi(x),
    J=sum_x chi(x)chi(1-x).

Then the exact identity is

    G(chi)^3 = q J,       J in Z[omega],       J conjugate(J)=q.

## Proof for every such finite field

Expand G(chi)^2 and group pairs x,y according to t=x+y. The t=0
contribution is chi(-1)sum_x chi(x)^2=0. For t nonzero substitute
x=tu,y=t(1-u), obtaining

    G(chi)^2 = J G(chi^2).

Next, in G(chi)G(chi^2), put x=ty with y nonzero. The inner sum of
psi(y(t+1)) over y nonzero is q-1 if t=-1 and -1 otherwise. Since
sum_t chi(t)=0 and chi(-1)=1, this gives

    G(chi)G(chi^2)=q.

Multiplying the first identity by G(chi) proves the cubic identity.
Complex conjugation of G(chi), followed by x -> -x, gives G(chi^2).
Consequently |G(chi)|^2=q and |J|^2=q. Since the summands defining J
are zero or powers of omega, J is an Eisenstein integer. Its field norm
is therefore q. Every step uses finite sums and character orthogonality.

## Prime-ideal generator and the negative sign

For an Eisenstein prime ideal away from 3 the residue field is either
F_p with p=1 modulo 3 or F_(p^2) with p=2 modulo 3. Identify cubic roots
in that field with 1,omega,omega^2 and choose chi(x)=x^((q-1)/3).
The reduction of J is

    sum_x x^a(1-x)^a,        a=(q-1)/3.

On expansion, each exponent lies between a and 2a, strictly between
0 and q-1. Every power sum is zero in F. Thus J belongs to the
prime ideal in question. Its norm is exactly the norm q of that ideal,
so it generates that ideal. Choosing the generator pi=-J gives

    G(chi)^3 = -q pi.

This prime-ideal assertion is restricted to the stated residue fields;
it is not an assertion that every field F_(p^f) is an Eisenstein prime
residue field. A different nontrivial additive character changes G by
a cubic root of unity and leaves its cube unchanged.

For coprime generators a,b, use the CRT representative
x=b v_b y+a v_a z, where b v_b=1 modulo a and a v_a=1 modulo b.
The additive character becomes the product psi_a(v_b y)psi_b(v_a z).
Changing variables in the two Gauss sums multiplies them by chi_a(b)
and chi_b(a), respectively. Hence

    G(ab)=chi_a(b)chi_b(a)G(a)G(b).

For a product m of distinct such prime generators, iteration gives the
product of the prime Gauss sums multiplied by cubic roots of unity.
Cubing removes those factors.
Hence, with compatible character and additive-character conventions,

    G(m)^3 = mu_K(m) N(m) m

for squarefree m built from those generators. This gives an exact
arithmetic encoding of the Möbius sign. It is the classical type of
identity used in the cubic-theta approach and is credited as such.

## What has and has not been closed

The finite-field and CRT identities above have proofs valid at every
allowed prime ideal. They do not bound the sums of the resulting cubic
Gauss coefficients, the off-diagonal correlations after Poisson summation,
or the required short-row mean square. Proving the arithmetic identity
does not establish the analytic estimate.

The exact checker covers all rational primes p=1 modulo 3 with 7<=p<=199.
It represents Z[omega] by pairs (a,b), computes J exactly, checks its norm
and its reduction, and verifies G^3=pJ as a polynomial identity modulo
1+X+...+X^(p-1). It uses no floating-point Gauss sums. The universal proof
is the finite-sum argument above; the checks are finite controls only.
