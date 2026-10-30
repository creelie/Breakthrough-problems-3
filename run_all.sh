#!/usr/bin/env bash
# run_all.sh: every check in this repository.
#   Python  checks/python/check.py  Chebyshev's bounds to 10^6, the parameters of the transfer theorem,
#                                   the arithmetic of Proposition 5.5, the count of Section 6, the
#                                   constants of Section 7 and of Appendix A, and the sizes M(chi) and
#                                   |L'/L(1,chi)| for small prime moduli (about twelve minutes)
#   Python  checks/python/eisenstein_check.py  the Gauss-sum and reciprocity identities of Lemma B.3
#                                   over Z[w] for 77 prime and 216 composite moduli (about four minutes)
#   C       checks/c/check.c        Chebyshev's bounds to 10^7, the parameters, the arithmetic of
#                                   Proposition 5.5 and Section 6 on a finer grid, and M(chi) for the
#                                   quadratic characters modulo the primes between 10^4 and 10^5
#   Lean    lean/                   the Lean 4 library (OpenAI's zero-free half-plane Re s > 7/8 with the
#                                   files it imports, and the deduction of the bounds for every character
#                                   from it) and the axiom check of lean/Axioms.lean, if lake is on PATH
#                                   and SKIP_LEAN is not 1; compiling OpenAI's 2,924 modules from source
#                                   takes several hours on four cores and about 10 GB of disk
# Needs a C compiler and Python 3; Lean is optional.
# Exit status 0 means every check that ran passed.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
B="$ROOT/build"
mkdir -p "$B"
CC_BIN="${CC:-cc}"
step() { printf '\n=== %s\n' "$1"; }

step "C"
"$CC_BIN" -O2 -o "$B/check_c" "$ROOT/checks/c/check.c" -lm
"$B/check_c"

step "Python"
python3 -I "$ROOT/checks/python/check.py"
python3 -I "$ROOT/checks/python/eisenstein_check.py"

step "Lean"
if [ "${SKIP_LEAN:-0}" = 1 ] || ! command -v lake >/dev/null 2>&1; then echo "lean build skipped"; else
  ( cd "$ROOT/lean" && lake exe cache get >/dev/null 2>&1 || true )
  ( cd "$ROOT/lean" && lake build Vinogradov 2>&1 | tee "$B/lean.log" | grep -E "error|Build completed" ) || true
  if ! grep -q "Build completed successfully" "$B/lean.log" || grep -q "error" "$B/lean.log"; then
    echo "Lean build failed" >&2; exit 1
  fi
  ( cd "$ROOT/lean" && lake env lean Axioms.lean ) | tee "$B/axioms.txt"
  python3 -I - "$B/axioms.txt" <<'PY' || { echo "unexpected axioms" >&2; exit 1; }
import re, sys
text = " ".join(open(sys.argv[1]).read().split())
lists = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
allowed = {"propext", "Classical.choice", "Quot.sound"}
ok = len(lists) == 19 and all({a.strip() for a in l.split(",")} <= allowed for l in lists)
ok = ok and "sorryAx" not in text and "does not depend" not in text
print("axiom lists:", len(lists))
sys.exit(0 if ok else 1)
PY
  if grep -rnwE "sorry|admit|native_decide|bv_decide" "$ROOT/lean/Vinogradov" "$ROOT/lean/Vinogradov.lean" "$ROOT/lean/OAI"; then
    echo "sorry, admit, native_decide or bv_decide found" >&2; exit 1
  fi
fi

printf '\nall checks passed\n'
