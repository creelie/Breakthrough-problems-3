# Character sums with log log q outside a sparse set of characters

Deep Bhattacharjee. Version 5.0.0, 12 November 2026.

For a primitive Dirichlet character χ modulo q let M(χ) be the largest modulus of a partial sum
of χ. The paper proves, without hypothesis:

- **Theorem 1.1.** M(χ) ≤ c₁ ε⁻¹ √q log log q for all but c₂ (log q)^51 q^ε primitive characters
  modulo q, uniformly for 0 < ε ≤ 1.
- **Corollary 1.2.** At most c₂ (log q)^51 q^(c₁/τ) characters have M(χ) > τ √q log log q; all but
  exp(O((log log q)²)) characters satisfy M(χ) ≪ √q log q / log log q.
- **Theorem 1.3 (transfer).** A zero-free rectangle Re s > θ, |Im s| ≤ q for the twists χψ by
  characters of modulus up to (log q)^16 gives M(χ) ≤ c₄ (1 − θ)⁻¹ √q log log q.
- **Theorem 1.5.** |L'/L(1, χ)| ≤ c₅ ε⁻¹ (log log q + log(2/ε)) for all but O((log q/ε)^c q^ε) characters.

The bound for every character remains open; it would follow from a zero-free half-plane
(Corollary 1.4). Section 7 reports M(χ) for all 5,733,937 nonprincipal characters to prime moduli
below 10^4.

## Contents

- `dist/PVPaper.pdf`, `dist/PVTeX.zip`: the paper (17 pages) and its source (one `main.tex` and `figures/*.png`).
- `paper/`: the same source; `figures/make_figures.py` draws the figures from `data/`.
- `c/mchi.c`, `c/mchi2.c`: M(χ) for all characters to prime moduli below 10^4; output in `data/`.
- `julia/check.jl`: independent recomputation of the largest M(χ)/√q for every prime q < 10^4 (compared with `data/mall.txt`) and the Gamma bound of Lemma 2.6; `julia/small.jl`: the data of Appendix A.
- `lean/PVChecks.lean`: the integer arithmetic of the proofs, core Lean 4 only.
- `run_all.sh`: compiles the C programs, recomputes the moduli below 1000 and compares with `data/mall.txt`, and checks the Lean file if `lean` is on the path.

Concept DOI: [10.5281/zenodo.23383715](https://doi.org/10.5281/zenodo.23383715).
