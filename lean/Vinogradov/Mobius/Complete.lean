import OAI.NumberTheory.DirichletL.Nonvanishing
import Vinogradov.Mobius.Main

/-! Closed endpoint using the credited, vendored OpenAI theorem. This removes
an unproved nonvanishing hypothesis from the endpoint; it does not remove
OpenAI's mathematical contribution or provide an independent zero-free proof. -/

noncomputable section
namespace Vinogradov.Mobius

open Complex

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

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.smoothed_mobius_bound
