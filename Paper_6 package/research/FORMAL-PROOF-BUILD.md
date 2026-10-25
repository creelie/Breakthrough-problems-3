# Rechecking the bundled credited formal proof

This source archive preserves the authorship and notices of the supplied
Paper 6 formal proof. It is not an independent replacement for OpenAI's
zero-free theorem. It contains source files, not a cached toolchain or a new
build result. Generated PDFs and build artifacts are excluded.

Extract formal-proof-sources.zip into an empty directory. The root contains
LICENSE, NOTICE, lean/ and journal/paper6-annals-review/checks/.

With the Lean version in lean/lean-toolchain installed, a Linux shell can run:

```sh
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
lake env lean ../journal/paper6-annals-review/checks/EndpointAudit.lean
lake env lean ../journal/paper6-annals-review/checks/MobiusAudit.lean
```

Fetches use the standard dependencies pinned in lean/lake-manifest.json.
This is a substantial build. Do not interpret an unfinished build, a static
import inventory or a numerical test as a successful kernel check.

From the extracted root, the nonstandard source inventory can be reproduced:

```sh
python journal/paper6-annals-review/checks/source_inventory.py source-inventory.json
```

The existing CI workflows in .github/workflows/ record the complete build,
report and negative-control gates. Formal coverage is mapped in
journal/paper6-annals-review/PROOF-COVERAGE.md. If that file is absent in an
older nested copy, use the separately supplied PROOF-COVERAGE.md from the
current research supplement, whose date and scope are explicit.

Historical full audit: commit 5c06ee00f451d7a79ba579fea4b960156f3611a9,
https://github.com/creelie/Breakthrough-problems-3/actions/runs/40145560153.
The current closure-pass check verifies the matching source tree and recorded
report digests; it does not claim a new full build.
