# Attribution and proof provenance

Deep Bhattacharjee and Ushashi Bhattacharya are the manuscript authors.
The original repository and its Apache 2.0 license are retained.

OpenAI's stronger zero-free result is cited directly: The quasi-Riemann
hypothesis: a zero-free half-plane Re(s)>7/8, 30 September 2026, Theorem 1.1,
with its formal Dirichlet nonvanishing declaration at:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean
The 11/12 input in this article is an elementary consequence of 7/8 < 11/12.
The theorem has a published preprint and formal source; it is not represented
as refereed or as a new proof by the present authors. The separate shorter
11/12 paper is not a dependency of this revision.

No third-party article is embedded or bundled in this manuscript. Appendix C
proves analytic implications of the cited theorem and explicitly retains that
dependency. Original OpenAI, Mathlib, PrimeNumberTheoremAnd and RellichKondrachov
notices remain in the parent repository's NOTICE and source trees.

The source-complete proof bundle includes those nonstandard source trees,
their NOTICE and their compatibility patches. Generic analytic helper
extractions in the new Möbius modules are credited in
lean/Vinogradov/Mobius/HELPER-PROVENANCE.json. Their inclusion is not a new
independent zero-free proof and does not transfer authorship to the article's
authors. The standard Mathlib dependencies are pinned, not relabelled.
