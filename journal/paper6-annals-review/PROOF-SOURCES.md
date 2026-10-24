# Rebuilding the proof from the supplied sources

The archive includes the nonstandard mathematical proof sources, including the
credited OpenAI nonvanishing proof. Its theorem is proved in the supplied Lean
development; it is not an additional axiom or a hypothesis of the closed
character-sum and Möbius endpoints. Reading or accepting the preprint PDF is not
a build prerequisite. OpenAI's authorship and the other source credits remain.

This is source completeness, not a new independent zero-free proof by the
manuscript authors. A clean rebuild still needs the pinned Lean toolchain,
Mathlib and its standard library dependencies, and disk space for their cache.
Those dependencies are listed by exact commit in `lean/lake-manifest.json`.
Their source/cache download needs network access on the first build. The package
does not claim to be an offline installation of Lean or Mathlib.

From the archive root, with Lean's `elan` installer and Python 3 available:

```sh
cd lean
lake exe cache get Mathlib
lake --no-cache build '+Vinogradov:olean'
lake env lean Axioms.lean > original-axioms.log
lake env lean ../journal/paper6-annals-review/checks/EndpointAudit.lean > endpoint-axioms.log
python ../journal/paper6-annals-review/checks/verify_axioms.py endpoint-axioms.log original-axioms.log full-audit.json
lake env lean ../journal/paper6-annals-review/checks/MobiusAudit.lean > mobius-axioms.log
python ../journal/paper6-annals-review/checks/verify_mobius_axioms.py mobius-axioms.log mobius-components.json
```

Stop immediately if any command fails; run the next command only after success.
`lake --no-cache build` builds the project proof modules from source rather than
substituting a downloaded project proof artifact. The preceding cache command
fetches the standard Mathlib dependencies.

`EndpointAudit.lean` states the ordinary character sum using Mathlib's
`DirichletCharacter`, finite sums and real logarithms. It also checks the
11/12 nonvanishing consequence, the exact revised Riesz exponent 2759/3000,
and the three closed Möbius conclusions. `MobiusAudit.lean` separately checks
the analytic implications, their arbitrary-boundary equivalence, and the
finite-sum identity. The verifier accepts only `propext`, `Classical.choice`
and `Quot.sound`; it rejects compiler errors, missing statements, `sorryAx`
and `ofReduceBool`.

The source inventory records each bundled Lean file's SHA-256 after LF
normalisation and checks that
all imports from the four nonstandard library roots resolve inside the package.
Regenerate it with:

```sh
python journal/paper6-annals-review/checks/source_inventory.py
```

For the article, run pdfLaTeX twice on `source/main.tex`. The TeX distribution
needs `aomart`, AMS packages, TikZ, `xurl` and Latin Modern. It includes four
vector figures. The PDF is one article; a separate third-party article is not
appended. Parameter and numerical checks are supplementary verification of
arithmetic and finite examples, not substitutes for the Lean proof.
