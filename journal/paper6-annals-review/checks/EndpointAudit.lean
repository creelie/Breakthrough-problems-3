import Vinogradov

/-!
Exact endpoint audit for the original formal development.

This file is a verification target until the full dependency build and its
axiom inspection succeed. It does not formalise every line of the separate
49-page written supplement or the independent replacement requested by the author.
-/

namespace Paper6.EndpointAudit

open Finset Complex
open scoped ArithmeticFunction.vonMangoldt

/-- The manuscript's main inequality in the standard Mathlib definitions. -/
theorem optimal_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤
          C * Real.sqrt q * Real.log (Real.log q) :=
  Vinogradov.PV.polya_vinogradov_loglog

/-- The weaker boundary follows from the original stronger formal theorem. -/
theorem eleven_twelfths_nonvanishing
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (11 / 12 : ℝ) < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  apply OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ
  · linarith
  · exact fun h => hχ h.1

/-- The Riesz estimate at the precise boundary used in the revised exposition. -/
theorem riesz_at_review_boundary :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
        ‖Vinogradov.Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤
          K * x ^ (2759 / 3000 : ℝ) * Real.log (q + 2) := by
  obtain ⟨K, hK, h⟩ := Vinogradov.Analytic.riesz_character_bound
    (e := 1 / 2000) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ x hx
  have hb := h q χ hχ (11 / 12 - 1 / 1000) (by norm_num) (by norm_num)
    (fun s hs => eleven_twelfths_nonvanishing χ hχ (by linarith)) x hx
  norm_num at hb ⊢
  exact hb

/-- Endpoint stated with a real summation limit, interpreted by its natural floor. -/
theorem real_endpoint_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 3 ≤ q → ∀ x : ℝ,
        ‖∑ n ∈ Ioc 0 ⌊x⌋₊, (χ n : ℂ)‖ ≤
          C * Real.sqrt q * Real.log (Real.log q) := by
  obtain ⟨C, hC, h⟩ := optimal_loglog_bound
  exact ⟨C, hC, fun q _ χ hχ hq x => h q χ hχ hq ⌊x⌋₊⟩

end Paper6.EndpointAudit

#print axioms Paper6.EndpointAudit.optimal_loglog_bound
#print axioms Paper6.EndpointAudit.eleven_twelfths_nonvanishing
#print axioms Paper6.EndpointAudit.riesz_at_review_boundary
#print axioms Paper6.EndpointAudit.real_endpoint_loglog_bound
