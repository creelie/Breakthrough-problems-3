# The Pólya–Vinogradov inequality with log log q

Deep Bhattacharjee (corresponding author; Formerly, Electro-Gravitational
Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India;
Formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India;
itsdeep@live.com, d.bhattacharjee@erl-forschung.de; ORCID 0000-0003-0466-750X)
and Ushashi Bhattacharya (Formerly, National Taiwan University, Taipei 106319,
Taiwan; rai.bhattacharya.in@gmail.com; ORCID 0009-0002-2254-3914).

Paper: [`preprintPolyaVinogradovLogLog/PolyaVinogradovLogLog.pdf`](preprintPolyaVinogradovLogLog/PolyaVinogradovLogLog.pdf).
Annals of Mathematics version (Hexagon 2610.00256v3): [`paper/paper1/PolyaVinogradovLogLog-Annals.pdf`](paper/paper1/PolyaVinogradovLogLog-Annals.pdf), source [`paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip`](paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip) (built from `paper/annals/`), submission files in [`journal/submission-annals/`](journal/submission-annals/); release v1.2.0: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0, Zenodo doi:[10.5281/zenodo.23563651](https://doi.org/10.5281/zenodo.23563651).
Lean formalisation and verification code on Zenodo: doi:[10.5281/zenodo.23383716](https://doi.org/10.5281/zenodo.23383716) (release v1.0.0; all versions: doi:[10.5281/zenodo.23383715](https://doi.org/10.5281/zenodo.23383715)).

## Results

**Theorem 1.1 (Pólya–Vinogradov with log log q).** There is an absolute
constant C such that for every primitive character χ modulo q ≥ 3 and every
x ≥ 1,

    |∑_{n ≤ x} χ(n)| ≤ C √q log log q.

Paley (1932) showed that log log q cannot be replaced by anything smaller, and
Montgomery and Vaughan (1977) proved the bound under the generalised Riemann
hypothesis. Their proof uses the hypothesis only on the major arcs, and the
zero-free half-plane Re s > 7/8 is enough there. On the minor arcs they use
their unconditional bound for exponential sums with multiplicative
coefficients; a weaker form suffices, and the paper proves it: there is C such
that for every completely multiplicative f with |f(n)| ≤ 1, every α, and
coprime a, r with |α − a/r| ≤ r^(-2) and 2 ≤ R ≤ r ≤ N/R,

    |∑_{n ≤ N} f(n) e(nα)| ≤ C (N/log N + N (log N)^2 / R^(1/4)).

**Theorem 1.3 (L'/L at s = 1 and Euler–Kronecker constants).** There is an
absolute constant C such that

- |L'/L(1, χ)| ≤ C log log q for every nonprincipal character χ modulo q, and
- −C log q log log q ≤ γ_q ≤ C log q for every prime q ≥ 3, where γ_q is the
  Euler–Kronecker constant of the cyclotomic field Q(ζ_q).

Under the generalised Riemann hypothesis the first bound is classical, Ihara
proved γ_q ≤ (2 + o(1)) log q and Badzyan proved a lower bound of the order of
the second; Ford, Luca and Moree proved both bounds without hypothesis for a
set of primes of density one. For all primes the best unconditional bound we
know was |γ_q| ≪_ε q^ε (Ihara, Murty and Shimura, Acta Arith. 137 (2009)).

The only input not proved in the paper is the zero-free half-plane
Re s > 7/8 for Dirichlet L-functions of nonprincipal characters (Theorem 1.2),
proved and formalised in Lean 4 by OpenAI ("The quasi-Riemann hypothesis: a
zero-free half-plane Re s > 7/8", 30 September 2026,
https://github.com/openai/math). That preprint is unrefereed; its Lean proof
is compiled here from source and checked by the Lean kernel together with ours,
so the whole chain is machine-checked.

## Earlier consequences of the half-plane in the Lean library

The Lean library also contains complete proofs of consequences of the
half-plane that others obtained first. They are not claimed as new and are not
in the paper.

- Least prime primitive root ≤ C_η (τ(p−1)^2 log(p+2))^(8+η), hence
  g*(p) = O_ε(p^ε) and Erdős Problem #985 for large primes. B. Sandlund
  (7 October 2026), J. Guo (8 October 2026,
  https://github.com/aster2024/openai-math-followups) and the zeta-lab notes
  (https://github.com/teal-sea/zeta-lab) give stronger bounds.
- The Lindelöf-type bound |L(s, χ)| + |L(s, χ)|^(-1) ≤ C_δ (q(3 + |t|))^δ for
  Re s ≥ 7/8 + δ, and ∑_{n ≤ x} χ(n) ≪_δ q^δ x^(7/8+δ) (zeta-lab, Hunt 125).
- ∑_{n ≤ x} χ(n) = o(x) uniformly in χ whenever log x / log log q → ∞, the
  range Granville and Soundararajan obtained under the generalised Riemann
  hypothesis; their method also gives it from the half-plane.

## Contents

| Path | Contents |
|---|---|
| `preprintPolyaVinogradovLogLog/` | the paper as a PDF |
| `paper/` | LaTeX source `pvloglog.tex` (IMPAN amsart template) with its figures in `paper/figures/` |
| `figures/` | TikZ sources of the figures and the scripts that generate them |
| `lean/` | Lean 4 project: `Vinogradov/` (this proof: `MV/` for the exponential sum bound, `PV/` for Theorem 1.1, `EulerKronecker/` for Theorem 1.3, `Final.lean`, `CharacterSums.lean` and `PV/Range.lean` for the earlier consequences), OpenAI's `OAI/` sources with the `PrimeNumberTheoremAnd/` and `RellichKondrachov/` files they import, the four Selberg sieve files of PrimeNumberTheoremAnd, and `Axioms.lean` |
| `checks/` | `check.py`, `check.jl`, `check.c`, `check.cpp`: four independent programs that check the numerical steps of the proofs |
| `run_all.sh` | runs the four programs, the Lean build and the axiom check |
| `make_dist.sh` | builds `dist/` and the master zip |
| `journal/JOURNAL.md` | target journal (Acta Arithmetica), format and policy |
| `journal/submission-acta/` | the submission: PDF, source zip, cover letter, checklist |
| `dist/` | `PolyaVinogradovLogLog_final2.pdf`, `PolyaVinogradovLogLog_final2-tex.zip` (source with PNG figures) and `PolyaVinogradovLogLog_final2-arxiv.tar.gz` |
| `MasterPolyaVinogradovLogLog_masterzipfinal2.zip` | every tracked file of the repository with `dist/` |
| `NOTICE` | provenance and licences of the third-party Lean sources |

## Lean statements

In `lean/Vinogradov/PV/Main.lean`, namespace `Vinogradov.PV` (Theorem 1.1):

```lean
theorem polya_vinogradov_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q)
```

In `lean/Vinogradov/EulerKronecker/Final.lean`, namespace `Vinogradov`
(Theorem 1.3; the second theorem bounds γ_q − γ, the sum over the
nonprincipal characters):

```lean
theorem logDeriv_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        C * Real.log (Real.log (q + 2))

theorem sum_logDeriv_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime → 3 ≤ q → ∃ r : ℝ,
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 = r ∧
        -(C * Real.log q * Real.log (Real.log q)) ≤ r ∧ r ≤ C * Real.log q
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

`Vinogradov.zeroFree` discharges the zero-free hypothesis of these proofs with
OpenAI's theorem

```lean
theorem OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0
```

`lean/Axioms.lean` prints the axioms used by OpenAI's theorem, by
`Vinogradov.zeroFree`, by the four theorems above, by four steps of
`polya_vinogradov_loglog`, and by the theorems of the earlier consequences.
Its output (Lean 4.34.1, Mathlib v4.34.1) is

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
'Vinogradov.logDeriv_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Vinogradov.sum_logDeriv_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

so no `sorry` and no axiom beyond the three standard ones is used anywhere in
the chain.

## Running the checks

Requirements: elan (the toolchain `leanprover/lean4:v4.34.1` is read from
`lean/lean-toolchain`), python3, julia, a C compiler and a C++17 compiler.

    ./run_all.sh              # programs, Lean build, axiom check
    ./run_all.sh --skip-lean  # programs only

The four programs check Chebyshev's bounds, Selberg's weights in exact
rationals, the inequalities of the contour shift, the exponent arithmetic, the
bilinear and prime pair bounds of the minor arcs, the major arc parameters, the
block sieve counts N_j ≤ 393 · 2^j/(j+1), and the formula for L'/L(1, χ)
against reference values of the Euler–Kronecker constants computed from the
Hurwitz zeta function with mpmath, for every nonprincipal character modulo the
primes q ≤ 300 (Python) and q ≤ 1000 (Julia). Each program ends with
`ALL PASS`, and the script with `ALL CHECKS PASSED`.

`lake exe cache get` fetches the compiled Mathlib; OpenAI's 2,900 modules are
compiled from source, which takes several hours on four cores and about 20 GB
of disk.

## Licence

Apache License 2.0 (`LICENSE`). OpenAI's Lean sources and the files of
PrimeNumberTheoremAnd and rellich-kondrachov they import, and the Selberg
sieve files of PrimeNumberTheoremAnd, are Apache 2.0; `NOTICE` lists their
origins.
