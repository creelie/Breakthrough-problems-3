import Vinogradov.Analytic

namespace Vinogradov.Mobius.ReviewBoundary

open Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- The exact parameter conversion, with its nonvanishing input visible.
The closed audit instantiates this input with the credited theorem. -/
theorem riesz_at_boundary_of_nonvanishing
    (hzero : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, (11 / 12 : ℝ) < s.re → χ.LFunction s ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
        ‖Vinogradov.Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤
          K * x ^ (2759 / 3000 : ℝ) * Real.log (q + 2) := by
  obtain ⟨K, hK, h⟩ := Vinogradov.Analytic.riesz_character_bound
    (e := 1 / 2000) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ x hx
  have hb := h q χ hχ (11 / 12 - 1 / 1000) (by norm_num) (by norm_num)
    (fun s hs => hzero q χ hχ s (by linarith)) x hx
  norm_num at hb ⊢
  exact hb

end Vinogradov.Mobius.ReviewBoundary

#print axioms Vinogradov.Mobius.ReviewBoundary.riesz_at_boundary_of_nonvanishing
