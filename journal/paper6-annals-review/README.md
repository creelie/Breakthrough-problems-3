# Paper_6: source-complete verification edition

**The optimal log log q bound in the Pólya–Vinogradov inequality**

Deep Bhattacharjee and Ushashi Bhattacharya · 25 October 2026

Current article: **Polya_Vinogradov_Annals_2026-10-25.pdf** (29 pages).
Verified earlier preprint: https://hexagonmath.org/2610.00256v2 .
Repository: https://github.com/creelie/Breakthrough-problems-3 .

This is one article in aomart screen format without margin line numbers. No
third-party article is appended. The complete nonstandard Lean proof sources
are supplied, including OpenAI's credited 7/8 Dirichlet nonvanishing proof.
The proof-source package therefore does not require accepting a preprint PDF
as an unproved premise. Standard Lean/Mathlib dependencies are pinned.

The article derives C sqrt(q) log log(q) for primitive characters, logarithmic
derivative bounds and cyclotomic Euler–Kronecker bounds. Appendix C proves and
formalises the smoothed Möbius equivalence for any fixed 0<theta<1, including
the explicit C_W q^104 X^(11/12) consequence and X^(7/8+epsilon) for fixed
nonprincipal characters. A formal identity connects the analytic sum with the
ordinary finite sum. The exact closed endpoints invoke the supplied credited
zero-free proof, rather than assume nonvanishing as an extra axiom.

This edition does **not** claim a newly discovered independent zero-free proof
by the manuscript authors. The equivalence cannot be used circularly to create
one. Attribution and source provenance remain in FORMAL-PROVENANCE.md,
THIRD-PARTY-NOTICES.md, the repository NOTICE and source headers.

Read PROOF-COVERAGE.md for the exact verified statements and current status,
and PROOF-SOURCES.md for rebuild commands and library pins. Successful source
compilation, finite numerical checks and peer review have different scopes.
The cover letter is unsent. No journal or arXiv submission is performed here.
At the author's request, this current research revision is being archived
while the fresh closed endpoint audit continues. Its pending status is retained
explicitly; it is not relabelled as passed. The DOI receipt is recorded after
publication, and the single final submission ZIP is created only after the
published archive is checksum-verified.

Current audit update, 25 October 2026: the complete source build and all
19 original plus seven closed endpoint axiom reports passed at commit
5c06ee00f451d7a79ba579fea4b960156f3611a9. The separate analytic audit passed all 20 named
statements. Both source-tree hashes match the current Lean tree. The reports
contain only propext, Classical.choice and Quot.sound. Receipt and verified
artifact digest: verification/full-audit.json. This updates the earlier
pending status; it does not constitute a new independent zero-free proof or
a line-by-line formalisation of the written article. The existing v1.3.0
release accurately records the pending status at its publication time.
