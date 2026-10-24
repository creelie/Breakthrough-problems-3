# Paper_6: one manuscript, cited zero-free input

Title: The optimal log log q bound in the Pólya–Vinogradov inequality.
Authors: Deep Bhattacharjee and Ushashi Bhattacharya.
Public preprint: https://hexagonmath.org/2610.00256v2 .
Existing repository: https://github.com/creelie/Breakthrough-problems-3 .

The revised manuscript is a single article. The appended 49-page OpenAI paper
has been removed. The zero-free statement is cited precisely as Theorem 1.1
of OpenAI, The Quasi-Riemann Hypothesis, 5 October 2026, at the frozen source
linked in the bibliography. Only the needed Dirichlet nonvanishing conclusion
is invoked. The elementary passage to imprimitive levels is written out.

The authors' deductions after that input are presented in the main text.
Appendix A verifies explicit parameters; Appendix B gives the general transfer
from a fixed boundary below one. Unsuccessful independent attempts and build
status belong in separate research/verification notes, not a second paper
inside the manuscript. No length target is used to inflate the article.

An independent zero-free proof by the manuscript authors has not been obtained.
This does not mean the cited result has no proof: it has the external proof
and formal development attributed to OpenAI. The fresh full source and endpoint
audit of that development is still pending. Its success must be observed before
claiming a completed fresh formal verification. The 11/12 written presentation
is not formalised line by line by a check of the older 7/8 route.

The original numerical suite is checks/ in the repository root and runs with
`./run_all.sh --skip-lean` on Linux. It contains independently written Python,
Julia, C and C++ programs for finite checks. This packet's checks/ also contains
exact 11/12 parameter checks in those four languages and the Lean parameter
proofs. These numerical programs do not establish global nonvanishing.

The sources use aomart screen mode, without margin line numbers. Compile
source/main.tex twice with pdfLaTeX. The current PDF is
Polya_Vinogradov_Annals_CITED_REVIEW.pdf. The structural verifier rejects an appended
third-party article. No journal submission, final DOI or final ZIP is issued.
