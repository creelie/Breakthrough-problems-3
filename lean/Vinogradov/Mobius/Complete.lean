import OAI.NumberTheory.DirichletL.Nonvanishing
import Vinogradov.Mobius.Main
import Vinogradov.Mobius.GeneralForward
import Vinogradov.Mobius.FiniteSums

/-! Closed endpoint using the credited, vendored OpenAI theorem. This removes
an unproved nonvanishing hypothesis from the endpoint; it does not remove
OpenAI's mathematical contribution or provide an independent zero-free proof. -/

noncomputable section
namespace Vinogradov.Mobius

open Complex
open scoped BigOperators

theorem smoothed_mobius_bound {W : ℝ → ℂ} (hW : IsTestWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ X : ℝ, 1 ≤ X →
        ‖smoothedSum χ W X‖ ≤ C * (q : ℝ) ^ (104 : ℕ) * X ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, h⟩ := smoothed_mobius_bound_of_seven_eighths hW
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ X hX
  apply h q χ hχ (fun s hs => ?_) X hX
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs
    (fun hpole => hχ hpole.1)

theorem smoothed_mobius_cancellation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ‖smoothedSum χ W X‖ ≤ C * X ^ ((7 / 8 : ℝ) + ε) := by
  apply smoothed_bounds_of_nonvanishing χ hχ (by norm_num : (0 : ℝ) < 7 / 8)
    (by norm_num : (7 / 8 : ℝ) < 1) (fun s hs => ?_) hW hε
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs
    (fun hpole => hχ hpole.1)

theorem finite_smoothed_mobius_bound {W : ℝ → ℂ} (hW : IsTestWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ X : ℝ, 1 ≤ X → ∀ N : ℕ, 2 * X ≤ N →
        ‖∑ n ∈ Finset.range N, coefficient χ n * W ((n : ℝ) / X)‖ ≤
          C * (q : ℝ) ^ (104 : ℕ) * X ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := smoothed_mobius_bound hW
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ X hX N hN
  rw [← smoothedSum_eq_sum_range χ hW (lt_of_lt_of_le zero_lt_one hX) N hN]
  exact hb q χ hχ X hX

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.smoothed_mobius_bound
#print axioms Vinogradov.Mobius.smoothed_mobius_cancellation
#print axioms Vinogradov.Mobius.finite_smoothed_mobius_bound
