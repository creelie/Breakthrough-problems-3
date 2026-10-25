# Source provenance and outside verification reports

Frozen official source: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean

All 2,924 locally vendored DirichletL Lean files have the same Git blobs as the
official source at both 1581d4cbdd69a0faf34b2089614fe2a814316a6a and adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Neither comparison found a changed local file or a local file absent upstream.
Two additional upstream Hecke wrapper files are not in the vendored snapshot;
they are listed in the receipts. This is a complete comparison of that source
subtree, not a claim that every upstream project file was compared. A source
match proves provenance; it is not a substitute for a successful kernel audit.

Receipts: verification/upstream-lean-provenance.json and
verification/upstream-lean-provenance-adc7f1241b42.json. They record their source
snapshot, counts, and scope. The current fresh build is recorded separately.

Two outside reports were read at fixed revisions. These are external reports,
not results of the current endpoint audit and not new independent proofs.

- https://github.com/davegoldblatt/openai-zeta-proof-check/tree/3f11b2203b76902f1b6b234115437302a94b79c3
  reports an independent rebuild, exact comparison and both Lean and nanoda
  kernel checks for the zeta endpoint. Its second-kernel result concerns zeta,
  not every Dirichlet character. The reported axiom closure is the three
  standard Lean axioms. Its source pin is adc7f1241b42e322a6451854ab7e4b4c146bf78a.
- https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/tree/b83a73c6cb626a391e551baafdb7d0cceafaa55a
  reports a full rebuild and axiom inspection for both zeta and Dirichlet
  nonvanishing, using that same source pin. It does not claim a different
  analytic proof or complete line-by-line review of the written paper.

The source equality connects those pins; it does not extend either report's
stated scope. This packet does not present an outside report as its own audit.

The original Linux source rebuild completed successfully with 19 standard-axiom
reports, including the credited nonvanishing theorem. Its separate revised
wrapper audit failed on a Riesz notation syntax error, now repaired. The
historical receipt preserves that failure rather than converting it into a
pass. The new current-root audit and analytic component audit are separate.
The source inventory checks all 2,997 bundled Lean files and their nonstandard
import closure. Standard-library commits are pinned in lake-manifest.json.
New generic helper extractions retain their OpenAI provenance in
lean/Vinogradov/Mobius/HELPER-PROVENANCE.json.

Current audit update, 25 October 2026: the complete source build and all
19 original plus seven closed endpoint axiom reports passed at commit
5c06ee00f451d7a79ba579fea4b960156f3611a9. The separate analytic audit passed all 20 named
statements. Both source-tree hashes match the current Lean tree. The reports
contain only propext, Classical.choice and Quot.sound. Receipt and verified
artifact digest: verification/full-audit.json. This updates the earlier
pending status; it does not constitute a new independent zero-free proof or
a line-by-line formalisation of the written article. The existing v1.3.0
release accurately records the pending status at its publication time.
