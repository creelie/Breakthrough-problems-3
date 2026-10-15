/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The zero-free half-plane `Re s > 7/8` discharges the hypothesis `ZeroFree` of the bounds for
`L'/L(1, χ)` and for the Euler–Kronecker constants of the cyclotomic fields `ℚ(ζ_q)`.
-/
import Vinogradov.Final
import Vinogradov.EulerKronecker.Sum

namespace Vinogradov

/-- **Theorem (A).** `|L'/L(1, χ)| ≤ C log log (q + 2)` for every nonprincipal character `χ`
modulo `q`. -/
theorem logDeriv_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        C * Real.log (Real.log (q + 2)) :=
  EulerKronecker.logDeriv_one_le_of_zeroFree zeroFree

/-- **Theorem (B).** For every prime `q ≥ 3`, `γ_q - γ = ∑_{χ ≠ 1} L'/L(1, χ)` is a real number
`r` with `-C log q log log q ≤ r ≤ C log q`. -/
theorem sum_logDeriv_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime → 3 ≤ q → ∃ r : ℝ,
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 = r ∧
        -(C * Real.log q * Real.log (Real.log q)) ≤ r ∧ r ≤ C * Real.log q :=
  EulerKronecker.sum_logDeriv_one_of_zeroFree zeroFree

end Vinogradov
