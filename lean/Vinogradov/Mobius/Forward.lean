import Vinogradov.Mobius.Reciprocal
import Vinogradov.Mobius.MellinDecay

/-! Assembly of the forward smoothed Mobius estimate. The imported reciprocal
lemma has an explicit nonvanishing hypothesis. This file does not replace that
credited zero-free input with an independent proof. -/

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set MeasureTheory Filter Asymptotics ENNReal
open scoped Topology Classical LSeries.notation ArithmeticFunction.Moebius

theorem scaledSum_mellin_convergent_two {q : ℕ} (χ : DirichletCharacter ℂ q)
    {W : ℝ → ℂ} (hW : IsTestWeight W) : MellinConvergent (scaledSum χ W) (2 : ℂ) := by
  let positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℕ → ℝ → ℂ := fun n t => (t : ℂ) * (coefficient χ n * W ((n : ℝ) * t))
  have hconv := CompactMellin.compact_weight_mellin_convergent W hW.1 hW.vanishes (2 : ℂ)
  have hint (n : ℕ) : Integrable (f n) positiveMeasure := by
    simpa [f, positiveMeasure, IntegrableOn, show (2 : ℂ) - 1 = 1 by norm_num] using
      CompactMellin.weighted_term_integrable (coefficient χ) (coefficient_zero χ)
        W (2 : ℂ) hconv n
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖f n t‖ ∂positiveMeasure) := by
    simpa [f, positiveMeasure, show (2 : ℂ) - 1 = 1 by norm_num] using
      CompactMellin.weighted_terms_fubini (coefficient χ) (coefficient_zero χ)
        W (2 : ℂ) (coefficient_LSeriesSummable χ (by norm_num))
  have hcast (n : ℕ) : (∫⁻ t : ℝ, ‖f n t‖ₑ ∂positiveMeasure) =
      ‖∫ t : ℝ, ‖f n t‖ ∂positiveMeasure‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hint n).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (f n t)))]
    simp only [coe_nnnorm]
  have hfinite : (∑' n : ℕ, ∫⁻ t : ℝ, ‖f n t‖ₑ ∂positiveMeasure) ≠ ⊤ := by
    rw [funext hcast]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hsum.abs)
  have htotal : (∫⁻ t : ℝ, ‖∑' n : ℕ, f n t‖ₑ ∂positiveMeasure) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun n => (hint n).aestronglyMeasurable.enorm)]
    exact hfinite.lt_top
  have hpoint (t : ℝ) : (∑' n : ℕ, f n t) = (t : ℂ) * scaledSum χ W t := by
    simp only [f, scaledSum, tsum_mul_left]
  have hcont := CompactMellin.weighted_sum_continuousOn_pos (coefficient χ) W
    (scaledSum χ W) hW.1 (fun y hy => hW.vanishes y (Or.inr hy))
    (fun t ht => scaledSum_hasSum χ W (fun y hy => hW.vanishes y (Or.inr hy)) (t := t) ht)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * scaledSum χ W t) positiveMeasure :=
    (Complex.continuous_ofReal.continuousOn.mul hcont).aestronglyMeasurable measurableSet_Ioi
  have hi : Integrable (fun t : ℝ => (t : ℂ) * scaledSum χ W t) positiveMeasure := by
    refine ⟨hmeas, ?_⟩
    simpa only [hpoint, HasFiniteIntegral] using htotal
  simpa [MellinConvergent, positiveMeasure, IntegrableOn,
    show (2 : ℂ) - 1 = 1 by norm_num] using hi

theorem scaledSum_mellin_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {W : ℝ → ℂ} (hW : IsTestWeight W)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (scaledSum χ W) s = mellin W s / χ.LFunction s := by
  have hM := smoothed_mellin_identity χ hW hs
  unfold smoothedSum at hM
  rw [mellin_comp_inv, neg_neg] at hM
  have hL : χ.LFunction s ≠ 0 := by
    intro hz
    have he := coefficient_euler_identity χ hs
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  exact (eq_div_iff hL).2 (by simpa only [mul_comm] using hM)

def forwardKernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ)
    (X : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((Real.log X : ℂ) * s) * mellin W s / χ.LFunction s

theorem inverse_power_eq_exp {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ((X⁻¹ : ℝ) : ℂ) ^ (-s) = Complex.exp ((Real.log X : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero hX.ne')),
    ← Complex.ofReal_log (inv_pos.mpr hX).le, Real.log_inv]
  congr 1
  push_cast
  ring

theorem forward_mellin_inversion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {W : ℝ → ℂ} (hW : IsTestWeight W)
    {X : ℝ} (hX : 0 < X)
    (hvertical : VerticalIntegrable (fun s => mellin W s / χ.LFunction s) 2) :
    smoothedSum χ W X = (1 / (2 * Real.pi)) •
      ∫ t : ℝ, forwardKernel χ W X ((2 : ℂ) + (t : ℂ) * I) := by
  have hFcont := CompactMellin.weighted_sum_continuousOn_pos (coefficient χ) W
    (scaledSum χ W) hW.1 (fun y hy => hW.vanishes y (Or.inr hy))
    (fun t ht => scaledSum_hasSum χ W (fun y hy => hW.vanishes y (Or.inr hy)) (t := t) ht)
  have hcont : ContinuousAt (scaledSum χ W) X⁻¹ :=
    (hFcont _ (inv_pos.mpr hX)).continuousAt (isOpen_Ioi.mem_nhds (inv_pos.mpr hX))
  have hV : VerticalIntegrable (mellin (scaledSum χ W)) 2 := by
    change Integrable (fun t : ℝ => mellin (scaledSum χ W) ((2 : ℂ) + (t : ℂ) * I))
    apply hvertical.congr
    filter_upwards with t
    exact (scaledSum_mellin_eq χ hW (s := (2 : ℂ) + (t : ℂ) * I) (by norm_num)).symm
  have hinv := mellinInv_mellin_eq 2 (scaledSum χ W) (inv_pos.mpr hX)
    (scaledSum_mellin_convergent_two χ hW) hV hcont
  change scaledSum χ W X⁻¹ = _
  rw [← hinv, mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [inverse_power_eq_exp hX, scaledSum_mellin_eq χ hW (by norm_num)]
  simp [smul_eq_mul, forwardKernel, mul_div_assoc]

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.scaledSum_mellin_convergent_two
#print axioms Vinogradov.Mobius.forward_mellin_inversion
