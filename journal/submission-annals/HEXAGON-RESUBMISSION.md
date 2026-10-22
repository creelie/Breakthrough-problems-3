# Hexagon (hexagonmath.org): version 3 of 2610.00256, with resubmission notes

Files to upload: `paper/paper1/PolyaVinogradovLogLog-Annals.pdf` (22 pages) and `paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip` (the source with `aomart.cls` and `figures/`; pdflatex compiles it on its own). All other fields are in `HEXAGON-FORM-FULL.md`. AI questions: text "a mix of human-written and AI-generated"; human understanding "some parts, but not all".

## Resubmission notes (the "changes in this version" field)

Relative to version 2 (2610.00256v2):

1. Theorems 1.1 and 1.3, their proofs and every lemma are unchanged.
2. The paragraph after Theorem 1.2 now names the Lean 4 theorem of OpenAI's formalisation of the zero-free half-plane Re s > 7/8, OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re, and states that the archive of the paper compiles these Lean sources unchanged together with the formalisation of the paper's own proofs, the Lean kernel accepting the theorem with no axioms beyond propext, Classical.choice and Quot.sound. The half-plane remains the one result used without proof and is credited to OpenAI.
3. The title-page footnote names both earlier versions, 2610.00256v1 and 2610.00256v2.
4. The archive of the Lean formalisation and the checking programs is cited as release v1.2.0, https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0, archived at Zenodo under doi:10.5281/zenodo.23563651.
