# Correction of the appended-paper edition

The earlier 78-page review appended a complete 49-page OpenAI article. That
was not an independent proof by these authors and was not a satisfactory
response to the requested self-contained manuscript. The appended article and
its title page have been removed. The current edition cites only the exact
zero-free theorem used, as the author subsequently authorised.

The earlier PDF is superseded. A recoverable copy is retained outside the
current submission packet in the local research workspace and Git history.
No final DOI or journal submission was made for that review edition.

The corrected PDF is Polya_Vinogradov_Annals_2026-10-25.pdf. The distinct
filename also prevents an open viewer from displaying the locked old edition
as though it were the newly corrected file.

Reverification of an existing proof is distinct from constructing an independent
proof. The full formal source and endpoint audit passed; the independent replacement remains
unobtained. Neither the page count nor the numerical checks change that status.

The current revision cites the formalised 7/8 theorem directly and adds a
written Möbius implication and converse in Appendix C. Neither replaces that
input with an independent proof. The older citation-only PDF is superseded.

The source-complete edition now supplies Lean implementations of the general
Möbius equivalence and finite-sum identity as well as the analytic bound. The
credited nonvanishing proof is included in the proof-source tree, not pasted
as another article. This does not change its authorship or claim a new
independent proof. The exact closed endpoints passed their separate release gate.

Current audit update, 25 October 2026: the complete source build and all
19 original plus seven closed endpoint axiom reports passed at commit
5c06ee00f451d7a79ba579fea4b960156f3611a9. The separate analytic audit passed all 20 named
statements. Both source-tree hashes match the current Lean tree. The reports
contain only propext, Classical.choice and Quot.sound. Receipt and verified
artifact digest: verification/full-audit.json. This updates the earlier
pending status; it does not constitute a new independent zero-free proof or
a line-by-line formalisation of the written article. The existing v1.3.0
release accurately records the pending status at its publication time.
