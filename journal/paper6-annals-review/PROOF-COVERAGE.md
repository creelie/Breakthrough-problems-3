# Proof coverage

The following are exact formal statements, not a claim that every sentence of
the article has a one-to-one Lean translation.

| Claim | Formal location | Verification record |
|---|---|---|
| Credited 7/8 nonvanishing for all Dirichlet characters, with the stated principal pole exception | OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re | Original clean source build and 19 axiom reports passed; verification/original-source-audit.json |
| Uniform primitive character bound C sqrt(q) log log(q), q>=3 | Vinogradov.PV.polya_vinogradov_loglog | Included in the original 19 reports; current closed wrapper audit pending |
| Weak Montgomery–Vaughan bound and harmonic-sum argument | Vinogradov.MV.weak_mv; Vinogradov.PV.hsum_bound | Included in the original 19 reports |
| Revised 11/12 boundary and exact Riesz exponent 2759/3000 | EndpointAudit.eleven_twelfths_nonvanishing; EndpointAudit.riesz_at_review_boundary | ReviewBoundary module passed locally; current closed wrapper audit pending |
| Nonvanishing iff all compact smooth Möbius bounds X^(theta+epsilon), for 0<theta<1 | Vinogradov.Mobius.nonvanishing_iff_smoothed_bounds | New analytic modules passed locally; current Linux component audit pending |
| Explicit reciprocal growth and C_W q^104 X^(11/12) implication | Vinogradov.Mobius.reciprocal_bound_of_nonvanishing; smoothed_mobius_bound_of_seven_eighths | Analytic modules passed; closed instantiation checked separately |
| Equality with the finite sum for N>=2X | Vinogradov.Mobius.smoothedSum_eq_sum_range | FiniteSums module passed locally |
| Closed Möbius bounds, including X^(7/8+epsilon) | Vinogradov.Mobius.smoothed_mobius_bound; smoothed_mobius_cancellation; finite_smoothed_mobius_bound | Current closed wrapper audit pending |
| Logarithmic derivative and sum of nonprincipal logarithmic derivatives | Vinogradov.logDeriv_one_le; Vinogradov.sum_logDeriv_one | Included in the original 19 reports |
| Identification of the latter sum with the cyclotomic Euler–Kronecker constant | Classical Dedekind zeta factorisation, cited Washington Theorem 4.3 | Written argument; not a separate Lean formalisation of cyclotomic Dedekind zeta |
| Every intermediate line of the rewritten 11/12 exposition or generic PV transfer Appendix B | Written analytic arguments | Not a line-by-line formalisation; the closed main inequality is formalised |
| A new independent zero-free proof by the manuscript authors | None | Not obtained or claimed |

The local module reports are verification/local-general-components.json.
The full build and current endpoint audit are a separate gate: a historical
successful source build must not be reported as a current successful audit
of newly added endpoints. The latest receipt will be stored beside these notes.
The earlier failed wrapper report is retained with its failure explicitly
labelled; a syntax error in that wrapper was repaired.

Only propext, Classical.choice and Quot.sound are permitted in the audited
axiom closures. No additional nonvanishing axiom is allowed. The negative
controls in checks/test_verify_axioms.py also check that the gate rejects
compiler errors, omitted endpoints, sorryAx and ofReduceBool.
