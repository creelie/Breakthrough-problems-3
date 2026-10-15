# The Pólya–Vinogradov inequality with log log q

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).

All versions on Zenodo: doi:10.5281/zenodo.0000000.

## Result

**Theorem (Pólya–Vinogradov with log log q).** There is C such that for every
primitive character χ modulo q ≥ 3 and every x ≥ 1,

    |∑_{n ≤ x} χ(n)| ≤ C √q log log q.

Paley (1932) showed that log log q cannot be replaced by anything smaller, and
Montgomery and Vaughan (1977) proved the bound under the generalised Riemann
hypothesis. Their proof uses the hypothesis only on the major arcs, and the
zero-free half-plane Re s > 7/8 is enough there. On the minor arcs they use
their unconditional bound for exponential sums with multiplicative coefficients
(Montgomery–Vaughan 1977, Corollary 1); a weaker form of it suffices, and the
paper proves it (Theorem 6.1):

**Theorem (exponential sums).** There is C such that for every completely
multiplicative f with |f(n)| ≤ 1, every α, and coprime a, r with
|α − a/r| ≤ r^(-2) and 2 ≤ R ≤ r ≤ N/R,

    |∑_{n ≤ N} f(n) e(nα)| ≤ C (N/log N + N (log N)^2 / R^(1/4)).

The proof follows Montgomery and Vaughan: a bilinear decomposition, the
spacing of the multiples of α, and Selberg's upper bound sieve for prime
pairs.

**Theorem (the range of o(x)).** There is C such that for every nonprincipal
character χ modulo q ≥ 3 and every x ≥ 2,

    |∑_{n ≤ x} χ(n)| ≤ Ψ(x, ⌈log q⌉^40) + C x / log q
                     ≤ C x (log log q / log x + 1 / log q),

where Ψ(x, y) counts the n ≤ x with no prime factor above y. So
∑_{n ≤ x} χ(n) = o(x) uniformly in χ whenever log x / log log q → ∞.
Granville and Soundararajan (J. Amer. Math. Soc. 14 (2001), Corollary A) proved
this under the generalised Riemann hypothesis and showed, unconditionally, that
the range cannot be enlarged: for every A > 0 and every prime q some
nonprincipal χ has |∑_{n ≤ x} χ(n)| ≫_A x at x = (log q)^A (their Theorem 3).
This is a direct consequence of the half-plane and the method of Granville and
Soundararajan: their Lemmas 8.1 and 8.2 assume only a zero-free rectangle
σ_0 ≤ Re z ≤ 1, and with σ_0 = 7/8 their deduction of Theorem 2 gives the bound
with log² q replaced by a larger power of log q. The proof here is shorter and
fully formalised: the integers with a prime factor above ⌈log q⌉^40 are handled
by the prime sums of the half-plane, the others by Chebyshev's bound
Ψ(x, y) log x ≤ x (1 + 2 log y + 2 log 4).

The paper also proves, with complete Lean proofs, consequences of the
half-plane that others obtained earlier (see Prior work below):

**Theorem (prime primitive roots).** For every η > 0 there is a constant C_η
such that every prime p has a prime primitive root ℓ with

    ℓ ≤ C_η (τ(p-1)^2 log(p+2))^(8+η),

where τ is the number of divisors. Hence g(p) ≤ g*(p) = O_ε(p^ε) (Vinogradov's
conjecture), and there is p_0 such that every prime p ≥ p_0 has a prime q < p
that is a primitive root modulo p (Erdős Problem #985 for large primes).

**Theorem (Lindelöf bound).** For every δ > 0 there is C_δ such that for every
nonprincipal character χ modulo q and every s = σ + it with σ ≥ 7/8 + δ,

    |L(s, χ)| + |L(s, χ)|^(-1) ≤ C_δ (q (3 + |t|))^δ.

**Theorem (character sums).** For every δ > 0 there is C_δ such that for every
nonprincipal character χ modulo q and every x ≥ 1,

    |∑_{n ≤ x} χ(n)| ≤ C_δ q^δ x^(7/8 + δ).

So ∑_{n ≤ x} χ(n) = o(x) uniformly for x ≥ q^η (Vinogradov's character sum
conjecture); Burgess's theorem gives this for prime q only when
x ≥ q^(1/4+ε).

The input is the zero-free half-plane Re s > 7/8 for Dirichlet L-functions of
nonprincipal characters, proved and formalised in Lean 4 by OpenAI ("The
quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8", 30 September 2026,
https://github.com/openai/math). The primitive root proof writes the indicator
of primitive roots as a sum of τ(p-1) groups of characters, bounds the prime sum
of each nonprincipal character by a Riesz mean and a contour shift into
Re s > 7/8, and compares with the principal character. The Lindelöf bound is
Littlewood's deduction from a zero-free half-plane (Borel–Carathéodory and
Hadamard's three circles), and the character sum bound follows from it by a
contour shift of the Riesz mean and an unsmoothing step.

## Prior work

- Primitive roots: B. Sandlund (research memo, 7 October 2026) derived
  g*(p) ≤ C_δ {k^2 (1 + log k)^2 log 2p}^(1/δ), k = ω(p-1), from a zero-free
  half-plane Re s > 1 − δ; J. Guo (8 October 2026,
  https://github.com/aster2024/openai-math-followups, Part II, §6.4) proved
  g*(p) ≪ k^16 (1 + log k)^16 (log p)^8 ≪ (log p)^24; and the zeta-lab notes
  (Hunt 125, 8 October 2026, https://github.com/teal-sea/zeta-lab) give the
  explicit bound (Λ_p log p)^8. These are stronger than the bound here, and
  Vinogradov's conjecture and #985 for large primes follow from each of them.
  What this repository adds for primitive roots is the complete Lean proof.
- Character sums: the Lindelöf-type consequence of the half-plane and the
  resulting o(x) for log x ≥ (log q)^(1−ε) are recorded in the zeta-lab notes
  (Hunt 125, §5), which leave the range x = (log q)^O(1) open.
- Other consequences of the half-plane: OpenAI (least quadratic nonresidue,
  Miller's test, class numbers, idoneal numbers), Guo (binary Goldbach
  exceptional set, least prime in a progression ≪ q^(7/3+ε)) and zeta-lab
  (Hunts 123 to 126).
- We have not found the Pólya–Vinogradov bound with log log q, or o(x) in the
  range log x / log log q → ∞ without the generalised Riemann hypothesis, in
  these sources or elsewhere.

## Scope

- The theorem rests on OpenAI's zero-free half-plane. That theorem is in an
  unrefereed preprint; its Lean proof is compiled here from source and checked
  by the Lean kernel together with ours, so the whole chain is machine-checked.
- The Lean proof of the Pólya–Vinogradov bound has no hypothesis: the
  exponential sum bound is `Vinogradov.MV.weak_mv`, proved in
  `lean/Vinogradov/MV/`, and the major arcs, Pólya's expansion and
  |τ(χ)| = √q are proved in `lean/Vinogradov/PV/`. The prime pair bound uses
  Arend Mellendijk's formalisation of Selberg's sieve from
  PrimeNumberTheoremAnd.
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
| `lean/` | Lean 4 project: `Vinogradov/` (this proof; `Final.lean` for primitive roots, `CharacterSums.lean` for the Lindelöf bound and character sums, `MV/` for the exponential sum bound, `PV/` for the Pólya–Vinogradov bound and, in `PV/Range.lean`, the range of o(x)), OpenAI's `OAI/` sources with the `PrimeNumberTheoremAnd/` and `RellichKondrachov/` files they import, the four Selberg sieve files of PrimeNumberTheoremAnd, and `Axioms.lean` |
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

In `lean/Vinogradov/MV/Weak.lean`, namespace `Vinogradov.MV`, with
`e x = exp(2πix)` and `q4 x = √√x` (the reduced fraction a/r is the rational
number `a` with denominator `a.den`):

```lean
theorem weak_mv : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ m n, f (m * n) = f m * f n) →
    (∀ n, ‖f n‖ ≤ 1) → ∀ (α : ℝ) (a : ℚ) (N : ℕ) (R : ℝ), 2 ≤ R → R ≤ a.den →
      (a.den : ℝ) ≤ N / R → |α - a| ≤ 1 / (a.den : ℝ) ^ 2 →
        ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ ≤
          C * (N / Real.log N + N * Real.log N ^ 2 / q4 R)
```

In `lean/Vinogradov/PV/Main.lean`, namespace `Vinogradov.PV`:

```lean
theorem polya_vinogradov_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q)
```

In `lean/Vinogradov/PV/Range.lean`, namespace `Vinogradov.PV`, with
`gpf n` the greatest prime factor of `n`:

```lean
theorem character_sum_psi :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ,
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          (((Ioc 0 x).filter (fun n => gpf n ≤ ⌈Real.log q⌉₊ ^ 40)).card : ℝ) +
            C * x / Real.log q

theorem character_sum_range :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ, 2 ≤ x →
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          C * x * (Real.log (Real.log q) / Real.log x + 1 / Real.log q)
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
`Vinogradov.zeroFree`, by the six theorems above, by `weak_mv`, by
`polya_vinogradov_loglog` and by four of its steps, and by the two theorems
of `Range.lean` and their step `nonsmooth_sum`. Its output (Lean 4.34.1,
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
'Vinogradov.MV.weak_mv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.mv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.polya_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.partial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.hsum_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.polya_vinogradov_loglog' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.nonsmooth_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.character_sum_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.PV.character_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound]
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
PrimeNumberTheoremAnd and rellich-kondrachov they import, and the Selberg
sieve files of PrimeNumberTheoremAnd, are
Apache 2.0; `NOTICE` lists their origins.
