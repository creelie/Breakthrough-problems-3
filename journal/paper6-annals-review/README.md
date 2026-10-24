# Paper_6: Pólya-Vinogradov with a credited zero-free input

Title: The optimal log log q bound in the Pólya-Vinogradov inequality.
Authors: Deep Bhattacharjee and Ushashi Bhattacharya.
Public preprint: https://hexagonmath.org/2610.00256v2 .
Existing repository: https://github.com/creelie/Breakthrough-problems-3 .
Current PDF: Polya_Vinogradov_Annals_MOBIUS_REVIEW.pdf.

This is one article. It cites OpenAI's formalised 7/8 nonvanishing theorem
directly and obtains the weaker 11/12 boundary by 7/8 < 11/12. The exact
declaration is OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean
It already covers imprimitive characters, with only the principal pole
exception. No argument from the separate shorter 11/12 paper is needed.
No third-party article is appended or included as another author's work.

Appendix A checks the explicit parameters. Appendix B proves the transfer from
any fixed uniform zero-free boundary below one. Appendix C supplies a complete
written deduction of smoothed twisted Möbius cancellation from nonvanishing,
including polynomial reciprocal growth, the contour shift, and the converse.
In particular, the cited 7/8 theorem gives
|sum mu(n) chi(n) W(n/X)| <= C_W q^104 X^(11/12)
for nonprincipal chi modulo q and smooth complex W supported inside (1,2).
It also gives O(chi,W,epsilon)(X^(7/8+epsilon)). These are consequences of the
credited theorem. The equivalence shows that they cannot then serve as an
independent replacement for the same theorem. No new zero-free proof is claimed.
The new Möbius deductions are written analytic proofs, not new Lean theorems.

The original full formal development and four exact endpoints are undergoing
a fresh source build and axiom audit. Until success is recorded, this is a
pending audit. The 11/12 written presentation is not formalised line by line by
checking the older 7/8 development. FORMAL-PROVENANCE.md records source matches
and the precise, different scopes of outside verification reports.

The original numerical suite is checks/ at repository root and runs with
./run_all.sh --skip-lean on Linux. It contains Python, Julia, C and C++ checks.
This packet's checks/ adds exact 11/12 parameter checks in those languages and
three Lean parameter statements. Finite tests do not prove global nonvanishing.

The source uses aomart screen mode, without margin line numbers. Compile
source/main.tex twice with pdfLaTeX. No page target is used to inflate the work.
The structural verifier checks attribution and rejects an appended article;
it does not certify mathematical truth. No final DOI, final ZIP or journal
submission has been made for this revision.
