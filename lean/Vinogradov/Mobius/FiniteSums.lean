import Vinogradov.Mobius.MellinCriterion

noncomputable section
namespace Vinogradov.Mobius

open Finset
open scoped Classical

/-- The formal series is literally the finite sum used in the manuscript.
The n=0 coefficient vanishes, and support eliminates every n>=N. -/
theorem smoothedSum_eq_sum_range {q : ℕ} (χ : DirichletCharacter ℂ q)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {X : ℝ} (hX : 0 < X)
    (N : ℕ) (hN : 2 * X ≤ N) :
    smoothedSum χ W X =
      ∑ n ∈ range N, coefficient χ n * W ((n : ℝ) / X) := by
  have htail (n : ℕ) (hn : n ∉ range N) :
      coefficient χ n * W ((n : ℝ) * X⁻¹) = 0 := by
    have hnn : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hnn
    have hdiv : 2 ≤ (n : ℝ) / X := (le_div_iff₀ hX).mpr (hN.trans hnr)
    have hw := hW.vanishes ((n : ℝ) / X) (Or.inr hdiv)
    simpa only [div_eq_mul_inv, mul_zero] using congrArg (coefficient χ n * ·) hw
  unfold smoothedSum scaledSum
  rw [tsum_eq_sum htail]
  simp only [div_eq_mul_inv]

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.smoothedSum_eq_sum_range
