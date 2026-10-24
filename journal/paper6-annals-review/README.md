# Paper_6 — Annals author-review edition

Title: The optimal log log q bound in the Pólya–Vinogradov inequality.
Authors: Deep Bhattacharjee and Ushashi Bhattacharya, preserving the public
preprint byline. Requested preprint: https://hexagonmath.org/2610.00256v2 .
Repository: https://github.com/creelie/Breakthrough-problems-3 .
No creelie/Paper_6 repository is used or created.

## Exact mathematical status

This is an author-review manuscript, not a certificate of a new independent
zero-free theorem or a claim of Annals acceptance. The manuscript includes
the complete 49-page attributed OpenAI 11/12 proof, rather than merely citing
its conclusion. This addresses an omitted external proof at the document
level. It does not establish an independent replacement for OpenAI's argument.
That second requested route remains unproved, with two precise attempted
substitutions and their barriers recorded in Appendix C.

The parameter conversion changes the prime-sum exponent to 49/50, the
smoothness cutoff to (ceil(log q))^1800, the cyclotomic cutoff to q^25,
the dyadic block denominator to 48, and the progression constant to 370200.
Appendix B proves the corresponding numerical deductions. Exact rational
checks and three fresh Lean proofs verify their stated parameter margins.
They do not themselves prove the full character-sum theorem.

The full previously bundled 7/8 source build is separate and incomplete at
this review snapshot. The new 11/12 parameter presentation is not yet fully
formalised end to end. Reproduction of the written zero-free proof does not
independently certify all of its analytic estimates. These limitations are
stated in the manuscript, not hidden in packaging metadata.

## Files and Annals format

Polya_Vinogradov_Annals_REVIEW.pdf is the review PDF. source/main.tex is its
independent build target. Four vector figures and their editable TikZ sources,
the frozen proof PDF and licenses are included. Compile from source/ using:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The aomart screen layout has no margin line numbering or false journal
publication header. The abstract is under 200 words; all main bibliography
entries are cited. The reproduced document retains its original reference
list and page labels. The main authors' PDF metadata and byline are preserved.
The additional AI contributions and their exact locations are disclosed.

COVER-LETTER-ANNALS.md is an unsent working draft. SUBMISSION-STATUS.md records
what must be resolved before describing this as a completed final submission.
No new DOI, final ZIP, journal submission or acceptance is asserted here.
The instruction to confirm a published DOI before a final ZIP is preserved.

The current review is 78 pages, including the unchanged 49-page credited proof.
Appendix D supplies a conditional transfer theorem for any fixed boundary below
one, with explicit treatment of its uniform constants and small moduli. The
Mellin inversion proof now gives the horizontal and shifted vertical integral
bounds, and the contour caption identifies the indicated nontrivial zeros.

`checks/EndpointAudit.lean` states the exact original character-sum endpoint,
its real-endpoint form, the 11/12 boundary and the revised Riesz exponent in
standard Mathlib definitions. `checks/verify_axioms.py` rejects missing theorem
reports, any additional axiom and unaccepted reduction shortcuts. These are
full-audit targets until a successful build and axiom report are actually
recorded; supplying the files does not constitute a completed verification.
The manual full-proof CI job builds the original formal argument from source
and inspects all 19 original theorem reports plus these four endpoints.
The routine PR jobs have only the smaller TeX/inclusion and parameter scopes.
