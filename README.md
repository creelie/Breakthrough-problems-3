# Prime primitive roots below every power of p

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).

All versions on Zenodo: doi:10.5281/zenodo.0000000.

## Result

**Theorem.** For every η > 0 there is a constant C_η such that every prime p has
a prime primitive root ℓ with

    ℓ ≤ C_η (τ(p-1)^2 log(p+2))^(8+η),

where τ is the number of divisors.

**Corollary (Vinogradov's conjecture, prime form).** For every ε > 0 there is
C_ε such that every prime p has a prime primitive root ℓ ≤ C_ε p^ε. So the least
primitive root g(p) and the least prime primitive root g*(p) are both
O_ε(p^ε).

**Corollary (Erdős Problem #985 for large primes).** There is p_0 such that
every prime p ≥ p_0 has a prime q < p that is a primitive root modulo p.

The input is the zero-free half-plane Re s > 7/8 for Dirichlet L-functions of
nonprincipal characters, proved and formalised in Lean 4 by OpenAI ("The
quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8", 30 September 2026,
https://github.com/openai/math). OpenAI deduce from it that the least quadratic
nonresidue is O_ε(p^ε); the bound for primitive roots, and its prime form, are
proved here. The proof writes the indicator of primitive roots as a sum of
τ(p-1) groups of characters, bounds the prime sum of each nonprincipal
character by a Riesz mean and a contour shift into Re s > 7/8, and compares
with the principal character.

## Scope

- The theorem rests on OpenAI's zero-free half-plane. That theorem is in an
  unrefereed preprint; its Lean proof is compiled here from source and checked
  by the Lean kernel together with ours, so the whole chain is machine-checked.
- p_0 is effective but far beyond computation. The programs show g*(p) < p for
  every prime 3 ≤ p ≤ 10^8 (the largest value is g*(73189117) = 223). Erdős's
  question for the primes in [10^8, p_0) is open.
- Carella's unconditional claims g*(p) ≪ p^(5/log log p) and
  g*(p) = O((log p)^(1+ε)) contain errors; Remark 1.7 of the paper and checks
  F1, F2 of the programs show where.

## Contents

| Path | Contents |
|---|---|
| `paper/` | LaTeX source `primroot.tex` (amsart) and the compiled `primroot.pdf` |
| `lean/` | Lean 4 project: `Vinogradov/` (this proof), OpenAI's `OAI/` sources with the `PrimeNumberTheoremAnd/` and `RellichKondrachov/` files they import, and `Axioms.lean` |
| `checks/` | `check.py`, `check.jl`, `check.c`, `check.cpp`: independent numerical checks |
| `run_all.sh` | runs the four programs, the Lean build and the axiom check |
| `journal/JOURNAL.md` | target journal, format and policy |
| `dist/` | the paper PDF, the arXiv tarball and `MasterVinogradovPrimitiveRootZip.zip`, which holds every file of the repository |
| `NOTICE` | provenance and licences of the third-party Lean sources |

## Lean statements

In `lean/Vinogradov/Final.lean`, namespace `Vinogradov`:

```lean
theorem least_prime_primitive_root_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)) ^ (8 + η)

theorem least_prime_primitive_root_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε

theorem erdos_985_of_large :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1
```

`Vinogradov.zeroFree` discharges the hypothesis of `Vinogradov/Main.lean` with
OpenAI's theorem

```lean
theorem OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0
```

`lean/Axioms.lean` prints the axioms used by OpenAI's theorem, by
`Vinogradov.zeroFree` and by the three theorems above. Its output (Lean 4.34.1,
Mathlib v4.34.1) is

```
'OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.least_prime_primitive_root_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.least_prime_primitive_root_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.erdos_985_of_large' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so no `sorry` and no axiom beyond the three standard ones is used anywhere in
the chain.

## Running the checks

Requirements: elan (the toolchain `leanprover/lean4:v4.34.1` is read from
`lean/lean-toolchain`), python3, julia, a C compiler and a C++17 compiler.

    ./run_all.sh              # programs, Lean build, axiom check
    ./run_all.sh --skip-lean  # programs only

`lake exe cache get` fetches the compiled Mathlib; OpenAI's 2,900 modules are
compiled from source, which takes several hours on four cores and up to about
20 GB of disk. Each
program ends with `ALL PASS`, and the script with `ALL CHECKS PASSED`.

## Licence

Apache License 2.0 (`LICENSE`). OpenAI's Lean sources and the files of
PrimeNumberTheoremAnd and rellich-kondrachov they import are
Apache 2.0; `NOTICE` lists their origins.
