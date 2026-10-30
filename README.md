# The Pólya–Vinogradov inequality with log log q for every character

Deep Bhattacharjee and Ushashi Bhattacharya. Version 4, 30 October 2026.

Let χ be a primitive Dirichlet character modulo q ≥ 3 and let M(χ) be the largest modulus of
a partial sum ∑_{n ≤ x} χ(n). The Pólya–Vinogradov inequality bounds M(χ) by a constant times
√q log q; Paley showed that √q log log q is the most that can be hoped for, and Montgomery and
Vaughan proved that bound under the generalised Riemann hypothesis. The paper proves, with no
hypothesis:

- **Theorem 1.5.** M(χ) ≤ C √q log log q for every primitive character χ modulo q ≥ 3, and
  |L'/L(1, χ)| ≤ C log log q for every nonprincipal character χ modulo q ≥ 3, with an absolute
  constant C.
- **Theorem 1.1 (transfer).** If θ < 1 is fixed and the L-functions of the twists χψ of χ by
  the characters ψ of the moduli up to (log q)^16 have no zero in the rectangle Re s > θ,
  |Im s| ≤ 5q², then M(χ) ≤ C_θ √q log log q.
- **Theorem 1.2.** For every ε > 0 there is C_ε such that, for every q ≥ 3, at most q^ε of the
  primitive characters modulo q have M(χ) > C_ε √q log log q.
- **Theorem 1.4.** At most q^ε of the nonprincipal characters modulo q have
  |L'/L(1, χ)| > C_ε log log q.
- **Theorem 2.3 (zero-density).** For k ≥ 3, T ≥ 2 and 11/12 ≤ σ ≤ 1 the nonprincipal
  characters modulo k together have at most 10^12 (kT)^{12(1−σ)} (log kT)^9 zeros with
  Re s ≥ σ, |Im s| ≤ T. This is proved in full in Appendix A, with every constant written
  out, so that Theorems 1.1 to 1.4 rest on Chebyshev's bounds alone.
- **Theorem B.1 (OpenAI).** Every finite-order Hecke L-function over Q(√−3), and so every
  Dirichlet L-function, has no zero with Re s > 11/12. The theorem and its proof are due to
  OpenAI (*The quasi-Riemann hypothesis: a cubic theta argument with a fixed ray class
  character*, 5 October 2026, https://github.com/openai/math); Appendix B reproduces the proof
  in full, with credit to them; every input of that proof is a published theorem, so no
  statement of the paper rests on an unrefereed source. Theorem 1.5 is Theorem B.1 fed into the
  transfer theorem with θ = 11/12.
- **Theorem 1.6 (Euler–Kronecker constants, new in v4).** The Euler–Kronecker constant γ_m of
  the cyclotomic field Q(ζ_m) satisfies γ_m ≤ 12 log m + 36 log log m + C for every m ≥ 3, and
  γ_q ≥ −C log q log log q for every prime q ≥ 5, with an absolute constant C. Ihara proved the
  upper bound (2 + o(1)) log q only under the generalised Riemann hypothesis; the proof here uses
  the half-plane of Theorem B.1, the explicit formula and the Brun–Titchmarsh inequality.

The transfer theorem is proved by a contour shift for Riesz means of prime sums, a dissection
of the circle into major and minor arcs, and a weak form of the Montgomery–Vaughan bound for
exponential sums with multiplicative coefficients, proved with Selberg's sieve as the only
arithmetic input. The zero-density theorem is the Ingham–Montgomery argument with a Gaussian
mollifier kernel, a hybrid mean value over the characters and the height, and Jensen's formula.
The zero-free half-plane is proved by a mean square of twisted Möbius sums over the Eisenstein
integers, Poisson summation, the transformation of Kubota's cubic theta function and the
quadratic large sieve of Goldmakher and Louvel, with a finite iteration at smaller scales.

OpenAI's earlier preprint (*The quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8*,
30 September 2026) proves the wider half-plane Re s > 7/8 in Lean 4, checked by the Lean kernel
against Mathlib. That proof is compiled here from its source and checked again (see *The Lean
library* below), together with a Lean proof of the two bounds of Theorem 1.5 from it; it is an
independent check of Theorem 1.5 with a smaller constant, and no statement of the paper depends
on it.

The results were first made public on 15 October 2026 as release v1.0.0 of this repository
(concept DOI [10.5281/zenodo.23383715](https://doi.org/10.5281/zenodo.23383715); later versions
[10.5281/zenodo.23563651](https://doi.org/10.5281/zenodo.23563651),
[10.5281/zenodo.23629139](https://doi.org/10.5281/zenodo.23629139),
[10.5281/zenodo.23629649](https://doi.org/10.5281/zenodo.23629649),
[10.5281/zenodo.23637263](https://doi.org/10.5281/zenodo.23637263),
[10.5281/zenodo.23638793](https://doi.org/10.5281/zenodo.23638793),
[10.5281/zenodo.23671158](https://doi.org/10.5281/zenodo.23671158) and
[10.5281/zenodo.23672710](https://doi.org/10.5281/zenodo.23672710)); an earlier and incomplete
version of the paper appeared on Hexagon as [hexagon:2610.00256](https://hexagonmath.org/2610.00256)
on 15 October 2026 and was revised there on 21 October 2026. That version claimed the bound
for every character from the zero-free half-plane as an external input; release v2.0.0 proved
everything else in full and stated the every-character bound separately on the machine-checked
input; v3.0.0 ([10.5281/zenodo.23672710](https://doi.org/10.5281/zenodo.23672710), hexagon:2610.00256v3) reproduced the proof of the half-plane in the paper. This
version (v4.0.0, [10.5281/zenodo.23789368](https://doi.org/10.5281/zenodo.23789368); v4.0.1 adds a title-page footnote naming the preprint hexagon:2610.00256v3) adds Section 8 on Euler–Kronecker constants and a check of the arithmetic identities
of Appendix B, and leaves no statement resting on an unrefereed source.

## Layout

- `paper/main.tex`, `paper/app.tex`, `paper/appB.tex`, `paper/figures/`: the LaTeX source (amsart, single column), Appendix A, Appendix B and the four figures; `paper/main.pdf` the compiled paper (53 pages).
- `figures/make_figures.py`: draws the four figures to `paper/figures/` at 200 dpi (matplotlib).
- `dist/`: the paper as `PolyaVinogradovLogLog_final2.pdf`, its source zip and the arXiv tarball.
- `checks/python/check.py`: Chebyshev's bounds to 10^6, the parameters (3.1) and inequalities (3.2) of the transfer theorem in exact rationals, the arithmetic of Proposition 5.5, the count of Section 6 and the constants of Section 7, every numerical inequality of Appendix A, and the sizes M(χ)/(√q log log q) for the primes between 1000 and 4000 and |L'/L(1, χ)|/log log q for the primes up to 300 against reference values of the Euler–Kronecker constants (about twelve minutes).
- `checks/python/eisenstein_check.py`: the Gauss-sum and reciprocity identities of Lemma B.3 over the Eisenstein integers, for 77 prime moduli (norms 7 to 397) and 216 composite moduli (about four minutes).
- `checks/c/check.c`: Chebyshev's bounds to 10^7 by a sieve, the parameters and the arithmetic of Proposition 5.5 and Section 6 on a finer grid, and M(χ) for the quadratic characters modulo the primes between 10^4 and 10^5 against the Pólya bound.
- `lean/`: the Lean 4 library described below, with `Axioms.lean` and the recorded axiom report `lean/axioms.txt`.
- `NOTICE`: provenance and licences of the third-party Lean sources.
- `run_all.sh`: runs all of them.

## The Lean library

`lean/` is a Lake project on Lean 4.34.1 with Mathlib v4.34.1. It contains

- `OAI/`: OpenAI's Lean sources, restricted to the import closure of
  `OAI.NumberTheory.DirichletL.Nonvanishing` (2,924 modules), copied from the mirror
  https://github.com/creelie/math01-openAI at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
  with the files of `PrimeNumberTheoremAnd/` and `RellichKondrachov/` they import (`NOTICE`
  gives the commits and patches). The theorem is

  ```lean
  theorem OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
      (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬(χ = 1 ∧ s = 1)) :
      DirichletCharacter.LFunction χ s ≠ 0
  ```

  where `DirichletCharacter.LFunction` is Mathlib's Dirichlet L-function.
- `Vinogradov/`: a proof of the two bounds of Theorem 1.5 from that theorem, with the constant of θ = 7/8
  (`Vinogradov.zeroFree` in `Final.lean` discharges the zero-free hypothesis with it):

  ```lean
  theorem Vinogradov.PV.polya_vinogradov_loglog :
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
        3 ≤ q → ∀ T : ℕ,
          ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q)

  theorem Vinogradov.logDeriv_one_le :
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
          C * Real.log (Real.log (q + 2))
  ```

  (log log (q + 2) ≤ 6 log log q for q ≥ 3, so the second is Theorem 1.5 up to the constant),
  together with the weak Montgomery–Vaughan bound `Vinogradov.MV.weak_mv`, the bound on the
  Euler–Kronecker constants `Vinogradov.sum_logDeriv_one`, and consequences of the half-plane
  that others obtained first (prime primitive roots, a Lindelöf-type bound, character sums in
  short ranges), which are not in the paper. None of the Lean files contains `sorry`.

The build and the axiom check were run as follows, on four cores with 15 GB of memory:

    cd lean && lake exe cache get && lake build Vinogradov && lake env lean Axioms.lean

Result of that run (26 October 2026; the OpenAI library, 7,060 Lake jobs, built in about four hours, the
deduction in a further hour): `lake build Vinogradov` completed with no error and no `sorry`, and
`lake env lean Axioms.lean` printed, for each of the nineteen theorems listed in `lean/Axioms.lean`,
beginning with `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` and
`Vinogradov.PV.polya_vinogradov_loglog`,

    depends on axioms: [propext, Classical.choice, Quot.sound]

and nothing else; the full output is `lean/axioms.txt`.

## Running the checks

    ./run_all.sh              # C, Python, then the Lean build and axiom check if lake is on PATH
    SKIP_LEAN=1 ./run_all.sh  # C and Python only

Requirements: a C compiler and Python 3; elan for the Lean build (the toolchain is read from
`lean/lean-toolchain`). `lake exe cache get` fetches the compiled Mathlib; OpenAI's modules are
compiled from source, which takes several hours on four cores and about 10 GB of disk.

## Releases

Releases are published by the workflow `release.yml` from the Actions tab; it runs the C and
Python checks and attaches the paper files of `dist/`.

| Release | DOI |
| --- | --- |
| v4.0.1 | [10.5281/zenodo.23791644](https://doi.org/10.5281/zenodo.23791644) |
| v4.0.0 | [10.5281/zenodo.23789368](https://doi.org/10.5281/zenodo.23789368) |
| v3.0.0 | [10.5281/zenodo.23672710](https://doi.org/10.5281/zenodo.23672710) |
| v2.0.0 | [10.5281/zenodo.23671158](https://doi.org/10.5281/zenodo.23671158) |
| v1.6.0 | [10.5281/zenodo.23638793](https://doi.org/10.5281/zenodo.23638793) |
| v1.5.0 | [10.5281/zenodo.23637263](https://doi.org/10.5281/zenodo.23637263) |
| v1.4.0 | [10.5281/zenodo.23629649](https://doi.org/10.5281/zenodo.23629649) |
| v1.3.0 | [10.5281/zenodo.23629139](https://doi.org/10.5281/zenodo.23629139) |
| v1.2.0 | [10.5281/zenodo.23563651](https://doi.org/10.5281/zenodo.23563651) |
| v1.0.0 | [10.5281/zenodo.23383716](https://doi.org/10.5281/zenodo.23383716) |

Concept DOI of all versions: [10.5281/zenodo.23383715](https://doi.org/10.5281/zenodo.23383715).

## Authors

Deep Bhattacharjee (corresponding author), Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; Formerly, University of Calcutta (Heramba Chandra College), 23/49 Gariahat Road, Golpark, Kolkata 700029, West Bengal, India.
Emails: d.bhattacharjee@erl-forschung.de, itsdeep@live.com, egspl@proton.me (for questions about this repository).
ORCID: 0000-0003-0466-750X.

Ushashi Bhattacharya, Formerly, National Taiwan University, Taipei 106319, Taiwan.
Email: rai.bhattacharya.in@gmail.com. ORCID: 0009-0002-2254-3914.

## Licence

Apache License 2.0 (`LICENSE`). OpenAI's Lean sources and the files of PrimeNumberTheoremAnd
and rellich-kondrachov they import are Apache 2.0; `NOTICE` lists their origins.
