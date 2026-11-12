#!/usr/bin/env bash
# Recompute M(chi) for the primes below 1000 and compare with data/mall.txt; check lean/PVChecks.lean.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
B="$ROOT/build"; mkdir -p "$B"
"${CC:-cc}" -O2 -o "$B/mchi" "$ROOT/c/mchi.c" -lm
"$B/mchi" 5 1000 > "$B/m1000.txt"
python3 - "$B/m1000.txt" "$ROOT/data/mall.txt" <<'PY'
import sys
new = [l.split() for l in open(sys.argv[1])]
old = {l.split()[0]: l.split() for l in open(sys.argv[2])}
bad = 0
for r in new:
    o = old[r[0]]
    if r[2:4] != o[2:4] or r[6:] != o[6:] or abs(float(r[1]) - float(o[1])) > 1e-6:
        bad += 1; print("mismatch", r[0])
print(f"{len(new)} moduli below 1000 recomputed, {bad} mismatches")
sys.exit(1 if bad else 0)
PY
if command -v lean >/dev/null; then (cd "$ROOT/lean" && lean PVChecks.lean && echo "Lean: PVChecks.lean checked"); fi
