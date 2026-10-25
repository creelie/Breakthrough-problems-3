/-
Selected generic analytic helpers from OpenAI's math repository (Apache 2.0).
Source pin: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
The original proofs are retained with namespace changes, avoiding a dependency
on unrelated arithmetic modules for these generic analytic lemmas.
See HELPER-PROVENANCE.json for source files and excerpt boundaries.
-/
import Mathlib

noncomputable section
open Filter Asymptotics MeasureTheory Set Complex Metric
open scoped Topology Classical LSeries.notation ArithmeticFunction.Moebius

namespace Vinogradov.Mobius.TestWeight

noncomputable def bumpData : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

noncomputable def bump (y : ℝ) : ℝ := bumpData y

theorem bump_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) bump := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (bumpData : ℝ → ℝ)
  exact bumpData.contDiff (n := ⊤)

theorem bump_nonneg (y : ℝ) : 0 ≤ bump y := bumpData.nonneg

theorem bump_one : bump (3 / 2 : ℝ) = 1 := by
  change bumpData (3 / 2 : ℝ) = 1
  exact bumpData.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]
    exact bumpData.rIn_pos.le)

theorem bump_support (y : ℝ) (hy : y ≤ 1 ∨ 2 ≤ y) : bump y = 0 := by
  change bumpData y = 0
  apply bumpData.zero_of_le_dist
  rw [Real.dist_eq]
  change (1 / 4 : ℝ) ≤ |y - 3 / 2|
  rcases hy with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem bump_compact : HasCompactSupport bump := bumpData.hasCompactSupport

noncomputable def positiveExtension (y : ℝ) : ℝ :=
  1 + (y - 1) * Real.smoothTransition (2 * y - 1)

theorem positiveExtension_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) positiveExtension := by
  unfold positiveExtension
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => 2 * y - 1) := by fun_prop
  exact contDiff_const.add
    ((contDiff_id.sub contDiff_const).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp ht))

theorem positiveExtension_pos (y : ℝ) : 0 < positiveExtension y := by
  unfold positiveExtension
  by_cases hhalf : y ≤ 1 / 2
  · have ht : 2 * y - 1 ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos ht]
    norm_num
  · by_cases hone : 1 ≤ y
    · have ht : 1 ≤ 2 * y - 1 := by linarith
      rw [Real.smoothTransition.one_of_one_le ht]
      linarith
    · have hle := Real.smoothTransition.le_one (2 * y - 1)
      have hnonneg := Real.smoothTransition.nonneg (2 * y - 1)
      have hprod : (1 - y) * Real.smoothTransition (2 * y - 1) ≤ 1 - y := by
        exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans_eq (mul_one _)
      nlinarith

theorem positiveExtension_eq (y : ℝ) (hy : 1 ≤ y) :
    positiveExtension y = y := by
  unfold positiveExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * y - 1)]
  ring

noncomputable def weight (ρ : ℂ) (y : ℝ) : ℂ :=
  (bump y : ℂ) * Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))

theorem weight_smooth (ρ : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (weight ρ) := by
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (bump y : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp bump_smooth
  have hlog : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Real.log (positiveExtension y)) :=
    positiveExtension_smooth.log (fun y => ne_of_gt (positiveExtension_pos y))
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => (Real.log (positiveExtension y) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hlog
  have hexp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Complex.exp ((Real.log (positiveExtension y) : ℂ) * (-ρ))) :=
    (hc.mul contDiff_const).cexp
  exact hb.mul hexp

theorem weight_support (ρ : ℂ) (y : ℝ)
    (hy : y ≤ 1 ∨ 2 ≤ y) : weight ρ y = 0 := by
  simp [weight, bump_support y hy]

theorem weight_eq_cpow (ρ : ℂ) (y : ℝ) (hy : 0 < y) :
    weight ρ y = (y : ℂ) ^ (-ρ) * (bump y : ℂ) := by
  by_cases hy1 : y ≤ 1
  · simp [weight, bump_support y (Or.inl hy1)]
  · have hgy : positiveExtension y = y :=
      positiveExtension_eq y (le_of_lt (lt_of_not_ge hy1))
    rw [weight, hgy, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))]
    rw [← Complex.ofReal_log hy.le]
    ring

theorem weight_mellin_eq_bump (ρ : ℂ) :
    mellin (weight ρ) ρ = mellin (fun y : ℝ => (bump y : ℂ)) 0 := by
  have hpoint : Set.EqOn (weight ρ)
      (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) (Set.Ioi 0) := by
    intro y hy
    exact weight_eq_cpow ρ y hy
  rw [mellin]
  have heq :
      (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (ρ - 1) * weight ρ y) =
      mellin (fun y : ℝ => (y : ℂ) ^ (-ρ) * (bump y : ℂ)) ρ := by
    rw [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => by
      simp only [smul_eq_mul]
      rw [hpoint hy])
  simp only [smul_eq_mul]
  rw [heq]
  simpa only [smul_eq_mul, add_neg_cancel] using
    (mellin_cpow_smul (fun y : ℝ => (bump y : ℂ)) ρ (-ρ))

noncomputable def weightedBump (y : ℝ) : ℝ :=
  bump y / positiveExtension y

theorem weightedBump_continuous : Continuous weightedBump := by
  exact bump_smooth.continuous.div positiveExtension_smooth.continuous
    (fun y => ne_of_gt (positiveExtension_pos y))

theorem weightedBump_compact : HasCompactSupport weightedBump := by
  change HasCompactSupport (fun y : ℝ => bump y * (positiveExtension y)⁻¹)
  exact bump_compact.mul_right

theorem weightedBump_nonneg (y : ℝ) : 0 ≤ weightedBump y := by
  exact div_nonneg (bump_nonneg y) (positiveExtension_pos y).le

theorem weightedBump_nonzero : weightedBump (3 / 2 : ℝ) ≠ 0 := by
  simp [weightedBump, bump_one, positiveExtension_eq (3 / 2) (by norm_num)]

theorem weightedBump_integral_pos :
    0 < ∫ y : ℝ, weightedBump y := by
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    weightedBump_continuous weightedBump_compact weightedBump_nonneg
    weightedBump_nonzero

theorem weightedBump_eq_zero_of_nonpos (y : ℝ) (hy : y ≤ 0) :
    weightedBump y = 0 := by
  simp [weightedBump, bump_support y (Or.inl (by linarith))]

theorem mellin_bump_zero_eq_integral_weightedBump :
    mellin (fun y : ℝ => (bump y : ℂ)) 0 =
      (∫ y : ℝ, weightedBump y : ℝ) := by
  rw [mellin]
  have hpoint : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ ((0 : ℂ) - 1) • (bump y : ℂ) =
        (weightedBump y : ℂ) := by
    intro y hy
    by_cases hy1 : y ≤ 1
    · simp [weightedBump, bump_support y (Or.inl hy1)]
    · have hgy : positiveExtension y = y :=
        positiveExtension_eq y (le_of_lt (lt_of_not_ge hy1))
      simp [weightedBump, hgy, Complex.cpow_neg_one, smul_eq_mul,
        div_eq_mul_inv, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpoint y hy)]
  rw [integral_complex_ofReal]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    exact weightedBump_eq_zero_of_nonpos y (le_of_not_gt hy))

theorem weight_mellin_ne_zero (ρ : ℂ) : mellin (weight ρ) ρ ≠ 0 := by
  rw [weight_mellin_eq_bump, mellin_bump_zero_eq_integral_weightedBump]
  exact Complex.ofReal_ne_zero.mpr weightedBump_integral_pos.ne'


end Vinogradov.Mobius.TestWeight
