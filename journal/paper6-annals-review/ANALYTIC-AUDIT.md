# Written-argument audit, 24 October 2026

This record distinguishes hand checks of deductions from completed kernel
verification. “Checked below” means the displayed derivation was examined; it
does not certify every reference or every analytic estimate in the cited zero-free paper.
The full proof is not yet certified by this record.

| Step | Checked deduction | Scope or remaining obligation |
|---|---|---|
| Chebyshev estimates | Odd-integer binomial induction; Legendre's factorial inequality; positive partial summation; prime powers contribute at most 2 sqrt(x) log(x). | Elementary written deductions checked. |
| Selberg sieve | Diagonalisation of the quadratic form gives Q=1/S. Products fe in the weight bound are distinct because e is coprime to d and f divides d. Each lcm has at most 3^omega(d) ordered antecedents. | Elementary written deduction checked; agrees with the form used in the two counting applications. |
| Mellin inversion | The shifted vertical integral is at most pi y^(-U)/(U-1) on the left and pi y^U/U on the right. For fixed U the horizontal integrals vanish quadratically with height. Absolute convergence justifies exchanging the series and integral. | Expanded explicit proof added, including y=1. |
| Logarithmic derivative | The closed disc stays within the assumed zero-free region. A branch of log L is normalised at 2+it by the Euler product. Borel–Carathéodory and Cauchy's estimate give a bound logarithmic in conductor and height. | Conditional analytic deduction checked; it does not prove the nonvanishing hypothesis. |
| Riesz contour shift | The integrand is holomorphic in the shifted strip and bounded by a constant times x^sigma (1+abs(t))^(-3/2) log(q+2). The horizontal lengths are fixed; both vertical integrals converge absolutely. | Conditional written deduction checked. The exact revised Riesz exponent is also a pending endpoint audit target. |
| Unsmoothing | The difference identity has error at most h(h+1) log(2x). With h=x^(47/50), the principal exponent is 49/50-1/3000. Logarithmic errors and prime powers are smaller. | Exact exponent margin passed fresh Lean and independent rational checks. |
| Minor arcs | Checked the interval Cauchy expansion, spacing separation, prime-pair sieve and the dyadic small/large-prime estimates against the displayed ranges. | Written deduction examined. A full kernel audit of the original MV theorem is pending; the parameter tests alone do not verify it. |
| Character products | If a primitive chi modulo q agreed with a character of level r<q on the common units, CRT would make chi trivial on the kernel of reduction to gcd(q,r), contradicting its conductor. | No unproved assumption that chi times psi is nonprincipal is inserted here. |
| Major arcs | Each n is assigned to its unique largest prime. Character expansion has at most r terms with coefficient modulus at most one; partial summation and sum(m^(-49/50)) <= 50 M^(1/50) give the stated bound. | Conditional on the checked prime-sum deduction and the zero-free input. |
| Harmonic sum | Abel summation uses t w(t)<=1/t. Smooth terms enter twice and each is bounded by exp(11) log Y. With R=M^16 and Y=M^1800 the remaining major-arc power is M^(-2). | The old power 700 fails for this boundary; the negative control is retained. Small H and Y>=H give an empty nonsmooth sum. |
| Fourier endpoint | Primitive Gauss sums have modulus sqrt(q). The geometric denominator is replaced by its 1/(2 pi i theta) term with bounded remainder; four harmonic sums suffice. Small moduli are absorbed using log(log(3))>0. | The exact standard character-sum statement and real-floor endpoint are pending formal audit targets. |
| Logarithmic derivative at one | Dominated convergence is justified by sigma0<1. Splitting the integral at log(q+2)^(1/(1-sigma0)) gives the claimed log-log bound. | Conditional written deduction checked. The original formal theorem uses log(log(q+2)), whose conversion is explicitly shown in the manuscript. |
| Progression prime powers | For p<=z at most one p-power lies in (Mq,2Mq); p>z is handled by the sieve. Dyadic blocks, denominator 48 and constant 600 give C0=370200. | Rational constants checked. The primality of q and z<q are necessary hypotheses and remain explicit. |
| Cyclotomic tail | Orthogonality gives c(n)=(q-1)1[n=1 mod q]-1[q does not divide n]. The q^25 tail is bounded because 25(1-sigma0)>2; the low integral is bounded by 100 log q. | The factorisation of the cyclotomic Dedekind zeta function is an explicitly cited classical input. The sum of logarithmic derivatives is not silently identified with an unrelated formal definition. |
| Möbius implication and converse | Period sums give holomorphic polynomial growth of L. Harnack on nested discs bounds 1/L; compact smooth Mellin decay permits the contour shift. The reverse direction uses a weight chosen to be nonzero at a hypothetical zero. Radii 53/48 and 52/48 give the explicit q^104 loss. | New written proof from the credited theorem; not an independent replacement and not a Lean formalisation. |
| Generic fixed boundary | Appendix B chooses delta, a and eta before taking A eta>=36. All constants may depend on theta but not q, chi or x. The case a=1/2, empty nonsmooth sum and small q are explicit. | A conditional transfer proof, not an independent zero-free construction or a completed new formalisation. |

The central unconditional obligation is nonvanishing. It is now supplied by a precise external theorem citation,
not by reproducing the third-party article. Its mean-square estimate, theta transformation and transfer
estimates require more than a checksum or the elementary checks above. The
original stronger formal theorem is undergoing a source build and an exact
endpoint/axiom audit. No success receipt has been substituted for a running job.

Even a successful original formal audit would not establish a new independent
proof by the present authors, or formalise every line of the revised 11/12
presentation and the new Möbius appendix. Those distinctions remain necessary in a final assessment.
