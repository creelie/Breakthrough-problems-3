# Vinogradov's conjectures on primitive roots and character sums

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

**Theorem (Lindelöf bound).** For every δ > 0 there is C_δ such that for every
nonprincipal character χ modulo q and every s = σ + it with σ ≥ 7/8 + δ,

    |L(s, χ)| + |L(s, χ)|^(-1) ≤ C_δ (q (3 + |t|))^δ.

**Theorem (character sums).** For every δ > 0 there is C_δ such that for every
nonprincipal character χ modulo q and every x ≥ 1,

    |∑_{n ≤ x} χ(n)| ≤ C_δ q^δ x^(7/8 + δ).

**Corollary (Vinogradov's character sum conjecture).** For every η > 0 and
θ > 7/8 there is C such that |∑_{n ≤ x} χ(n)| ≤ C x^θ for every nonprincipal χ
modulo q and every x ≥ q^η. So ∑_{n ≤ x} χ(n) = o(x) uniformly for x ≥ q^η;
Burgess's theorem gives this for prime q only when x ≥ q^(1/4+ε).

**Theorem (Pólya–Vinogradov with log log q).** There is C such that for every
primitive character χ modulo q ≥ 3 and every x ≥ 1,

    |∑_{n ≤ x} χ(n)| ≤ C √q log log q.

Paley (1932) showed that log log q cannot be replaced by anything smaller, and
Montgomery and Vaughan (1977) proved the bound under the generalised Riemann
hypothesis. Their proof uses the hypothesis only on the major arcs, and the
zero-free half-plane Re s > 7/8 is enough there; on the minor arcs it uses their
unconditional bound for exponential sums with multiplicative coefficients
(Montgomery–Vaughan 1977, Corollary 1).

The input is the zero-free half-plane Re s > 7/8 for Dirichlet L-functions of
nonprincipal characters, proved and formalised in Lean 4 by OpenAI ("The
quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8", 30 September 2026,
https://github.com/openai/math). OpenAI deduce from it that the least quadratic
nonresidue is O_ε(p^ε); the bound for primitive roots, and its prime form, are
proved here. The proof writes the indicator of primitive roots as a sum of
τ(p-1) groups of characters, bounds the prime sum of each nonprincipal
character by a Riesz mean and a contour shift into Re s > 7/8, and compares
with the principal character. The Lindelöf bound is Littlewood's deduction from
a zero-free half-plane (Borel–Carathéodory and Hadamard's three circles), and
the character sum bound follows from it by a contour shift of the Riesz mean
and an unsmoothing step. OpenAI's paper and its companions (Artin's conjecture,
deterministic factorisation, 4 October 2026) state none of these results.

## Scope

- The theorem rests on OpenAI's zero-free half-plane. That theorem is in an
  unrefereed preprint; its Lean proof is compiled here from source and checked
  by the Lean kernel together with ours, so the whole chain is machine-checked.
- In the Lean proof of the Pólya–Vinogradov bound, Corollary 1 of
  Montgomery–Vaughan (1977) is the hypothesis `MVBound`; the paper cites it.
  Everything else in that proof, including the major arcs, Pólya's expansion
  and |τ(χ)| = √q, is checked by the Lean kernel.
- p_0 is effective but far beyond computation. The programs show g*(p) < p for
  every prime 3 ≤ p ≤ 10^8 (the largest value is g*(73189117) = 223). Erdős's
  question for the primes in [10^8, p_0) is open.
- Carella's unconditional claims g*(p) ≪ p^(5/log log p) and
  g*(p) = O((log p)^(1+ε)) contain errors; Remark 1.11 of the paper and checks
  F1, F2 of the programs show where.

## Contents

| Path | Contents |
|---|---|
| `paper/` | LaTeX source `primroot.tex` (amsart) and the compiled `primroot.pdf` |
| `lean/` | Lean 4 project: `Vinogradov/` (this proof; `Final.lean` for primitive roots, `CharacterSums.lean` for the Lindelöf bound and character sums, `PV/` for the Pólya–Vinogradov bound), OpenAI's `OAI/` sources with the `PrimeNumberTheoremAnd/` and `RellichKondrachov/` files they import, and `Axioms.lean` |
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

In `lean/Vinogradov/CharacterSums.lean`, namespace `Vinogradov.CharSum`:

```lean
theorem lindelof {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 7 / 8 + w ≤ s.re →
        ‖DirichletCharacter.LFunction χ s‖ + ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
          C * ((q : ℝ) * (3 + |s.im|)) ^ w

theorem character_sum_bound {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * (q : ℝ) ^ w * x ^ (7 / 8 + w)

theorem character_sum_le_rpow {η θ : ℝ} (hη : 0 < η) (hθ : 7 / 8 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ^ η ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * x ^ θ
```

In `lean/Vinogradov/PV/Main.lean`, namespace `Vinogradov.PV`, with
`e x = exp(2πix)`:

```lean
def MVBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α : ℝ) (a : ℚ) (N : ℕ)
    (R : ℝ), 2 ≤ R → R ≤ a.den → (a.den : ℝ) ≤ N / R → |α - a| ≤ 1 / (a.den : ℝ) ^ 2 →
      ‖∑ n ∈ Finset.Ioc 0 N, (χ n : ℂ) * e (n * α)‖ ≤
        C * (N / Real.log N + N * Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R)

theorem polya_vinogradov_loglog (hMV : MVBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Finset.Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q)
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
`Vinogradov.zeroFree`, by the six theorems above, by
`polya_vinogradov_loglog` and by three of its steps. Its output (Lean 4.34.1,
Mathlib v4.34.1) is

```
'OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.zeroFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.least_prime_primitive_root_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.least_prime_primitive_root_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.erdos_985_of_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.CharSum.lindelof' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.CharSum.character_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.CharSum.character_sum_le_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.polya_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.hsum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.polya_vinogradov_loglog' depends on axioms: [propext, Classical.choice, Quot.sound]
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
