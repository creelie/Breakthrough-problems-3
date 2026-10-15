# Priority check, 15 October 2026

Question: has anyone proved, before this paper, (1) the Pólya–Vinogradov bound
√q log log q for every primitive character without the generalised Riemann
hypothesis, or (2) |L'/L(1, χ)| ≪ log log q for every nonprincipal χ and the
two-sided bound −C log q log log q ≤ γ_q ≤ C log q for the Euler–Kronecker
constants of Q(ζ_q) for every prime q?

| Source | Checked | Finding |
|---|---|---|
| OpenAI, "The quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8" (https://github.com/openai/math, 30 September 2026) | the consequences the paper draws | least quadratic nonresidue, Miller's primality test, class numbers, idoneal numbers; neither (1) nor (2) |
| J. Guo, https://github.com/aster2024/openai-math-followups | README and Part II, 15 October 2026 | binary Goldbach exceptional set, least prime in a progression, least nonresidues, least primitive roots; neither (1) nor (2) |
| zeta-lab, https://github.com/teal-sea/zeta-lab | README, Hunts 123 to 126, 15 October 2026 | Linnik's constant, class numbers (h(D) ≥ √q/(10π log log q)), small witnesses, primes between powers; neither (1) nor (2) |
| Web search (Pólya–Vinogradov with log log q, unconditional; 2026) | 15 October 2026 | Montgomery–Vaughan 1977 under GRH; Granville–Soundararajan 2007 and Goldmakher 2012 for characters of fixed odd order; Mangerel, IMRN 2026, lower bounds for odd order; no unconditional √q log log q for all primitive characters |
| Web search (Euler–Kronecker constants of cyclotomic fields, unconditional) | 15 October 2026 | Ihara 2006 and Badzyan 2010 under GRH; Ford–Luca–Moree 2014 for a set of primes of density one; Ihara–Murty–Shimura 2009, γ_q of absolute value ≪_ε q^ε for all q; no bound of the form in (2) for all primes |
| OpenRefute problem dossiers (`Problems/` of the mirror creelie/trureturing-openrefute, snapshot of 10 October 2026, 782 files) | 15 October 2026 | one character sum entry, Zhang's question (D) on differences of Legendre sums (arXiv 2506.17235), unrelated; neither (1) nor (2) |

Conclusion: in the sources checked, neither (1) nor (2) appears before this
paper. Both rest on OpenAI's half-plane, which is in an unrefereed preprint
with a Lean 4 proof; the bound |L'/L(1, χ)| ≪ log log q is classical under
the generalised Riemann hypothesis, and the paper says so.
