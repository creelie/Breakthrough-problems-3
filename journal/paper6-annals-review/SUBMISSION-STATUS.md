# Submission status and remaining work

Prepared in the Annals aomart screen layout. The official guide checked on
24 October 2026 is https://annals.math.princeton.edu/submission-guidelines .
It accepts a PDF via https://ef.msp.org/submit/annals ; an arXiv identifier
is not required. Authors must remain human and disclose AI contributions by
location. The current abstract, main references, vector artwork and disclosure
were prepared against those requirements. No copyright agreement is signed.

Completed: complete credited proof inclusion; written 11/12 parameter
conversion; three exact Lean parameter proofs; independent rational checks;
successful local PDF build; both public authors retained; source provenance.

Not completed: a wholly independent zero-free replacement proof; a completed
fresh audit of the full vendored 7/8 proof; an end-to-end formalisation of the
new parameter presentation; an independent assessment of every analytic step
in the reproduced proof and of the manuscript's novelty and significance.
These are distinct obligations. Neither a page count nor an appended proof
is a substitute for them. The two simple independent substitutions examined
in Appendix C do not discharge them.

The authors should confirm whether any version is already under journal
consideration before submitting. No such status is inferred from old release
notes. A new Hexagon identifier will be added only after it is verified.
No final archive DOI or final ZIP is issued for this author-review state.

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
