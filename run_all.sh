#!/usr/bin/env bash
# Runs every check of "The Pólya–Vinogradov inequality with log log q":
# the Python, Julia, C and C++ programs, then the Lean build and the axiom check.
# Usage: ./run_all.sh [--skip-lean]
set -euo pipefail
cd "$(dirname "$0")"
for tool in python3 julia cc c++; do
  command -v "$tool" >/dev/null || { echo "missing tool: $tool" >&2; exit 2; }
done
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

echo "== Python";  python3 checks/check.py
echo "== Julia";   julia checks/check.jl
echo "== C";       cc -O2 -o "$tmp/check_c" checks/check.c -lm && "$tmp/check_c"
echo "== C++";     c++ -O2 -std=c++17 -o "$tmp/check_cpp" checks/check.cpp && "$tmp/check_cpp"

if [ "${1:-}" = "--skip-lean" ]; then echo "ALL NUMERICAL CHECKS PASSED (Lean skipped)"; exit 0; fi
command -v lake >/dev/null || { echo "missing tool: lake (install elan)" >&2; exit 2; }
echo "== Lean"
cd lean
lake exe cache get
lake build Vinogradov
lake env lean Axioms.lean | tee "$tmp/axioms.txt"
python3 - "$tmp/axioms.txt" <<'PY' || { echo "AXIOM CHECK FAILED" >&2; exit 1; }
import re, sys
text = " ".join(open(sys.argv[1]).read().split())
lists = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
allowed = {"propext", "Classical.choice", "Quot.sound"}
ok = len(lists) == 14 and all({a.strip() for a in l.split(",")} <= allowed for l in lists)
ok = ok and "sorryAx" not in text and "does not depend" not in text
print("axiom lists:", len(lists))
sys.exit(0 if ok else 1)
PY
echo "ALL CHECKS PASSED"
