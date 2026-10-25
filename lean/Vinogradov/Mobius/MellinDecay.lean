import Vinogradov.Mobius.MellinCriterion

/-! Smooth compact weights have Schwartz Mellin transforms on every vertical
line. All decay and integrability assertions in this file are proved from the
actual test weight, rather than supplied as hypotheses of a power-bound theorem. -/

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set MeasureTheory
open scoped Topology Classical FourierTransform SchwartzMap

def logarithmicProfile (σ : ℝ) (W : ℝ → ℂ) (v : ℝ) : ℂ :=
  Real.exp (-σ * v) • W (Real.exp (-v))

theorem logarithmicProfile_smooth (σ : ℝ) {W : ℝ → ℂ} (hW : IsTestWeight W) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (logarithmicProfile σ W) := by
  have hWs := hW.1
  unfold logarithmicProfile
  fun_prop

theorem logarithmicProfile_compact (σ : ℝ) {W : ℝ → ℂ} (hW : IsTestWeight W) :
    HasCompactSupport (logarithmicProfile σ W) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  change closure (Function.support (logarithmicProfile σ W)) ⊆ Icc (-1 : ℝ) 0
  apply closure_minimal ?_ isClosed_Icc
  intro v hv
  by_contra hnot
  have hzero : W (Real.exp (-v)) = 0 := by
    by_cases hv0 : 0 ≤ v
    · exact hW.vanishes _ (Or.inl (Real.exp_le_one_iff.mpr (by linarith)))
    · have hvlow : v < -1 := by
        by_contra hlow
        exact hnot ⟨le_of_not_gt hlow, (lt_of_not_ge hv0).le⟩
      exact hW.vanishes _ (Or.inr (by linarith [Real.add_one_le_exp (-v)]))
  exact hv (by simp [logarithmicProfile, hzero])

def logarithmicSchwartz (σ : ℝ) {W : ℝ → ℂ} (hW : IsTestWeight W) : 𝓢(ℝ, ℂ) :=
  (logarithmicProfile_compact σ hW).toSchwartzMap (logarithmicProfile_smooth σ hW)

def mellinFrequencyScale : ℝ ≃L[ℝ] ℝ where
  toFun t := t / (2 * Real.pi)
  invFun t := t * (2 * Real.pi)
  left_inv := by intro t; field_simp
  right_inv := by intro t; field_simp
  map_add' := by intro x y; ring
  map_smul' := by intro a t; simp only [smul_eq_mul, RingHom.id_apply]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def mellinSchwartz (σ : ℝ) {W : ℝ → ℂ} (hW : IsTestWeight W) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ mellinFrequencyScale
    (𝓕 (logarithmicSchwartz σ hW))

theorem mellin_eq_mellinSchwartz (σ t : ℝ) {W : ℝ → ℂ} (hW : IsTestWeight W) :
    mellin W ((σ : ℂ) + (t : ℂ) * I) = mellinSchwartz σ hW t := by
  rw [mellin_eq_fourier]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  rw [hre, him]
  rfl

theorem schwartz_one_add_norm_integrable (F : 𝓢(ℝ, ℂ)) (k : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * ‖F t‖) := by
  have hsum : Integrable (fun t : ℝ => ∑ i ∈ Finset.range (k + 1),
      (‖t‖ ^ i * ‖F t‖) * (Nat.choose k i : ℝ)) := by
    exact integrable_finsetSum _ (fun i _ => (F.integrable_pow_mul volume i).mul_const _)
  convert hsum using 1
  funext t
  rw [add_comm (1 : ℝ) |t|, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one, Real.norm_eq_abs]
  ring

theorem mellin_polynomial_weight_integrable (σ : ℝ) {W : ℝ → ℂ}
    (hW : IsTestWeight W) (k : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ k * ‖mellin W ((σ : ℂ) + (t : ℂ) * I)‖) := by
  simpa only [mellin_eq_mellinSchwartz σ _ hW] using
    schwartz_one_add_norm_integrable (mellinSchwartz σ hW) k

theorem rpow_between_endpoints (y a b u : ℝ) (hy : 0 < y) (ha : a ≤ u) (hb : u ≤ b) :
    y ^ u ≤ y ^ a + y ^ b := by
  by_cases h1 : 1 ≤ y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

/-- The generic compact-strip bound follows the elementary Mellin lemma in
OpenAI's `Mellin/VerticalContourShift.lean`, with retained attribution. -/
theorem mellin_uniform_strip_bound {W : ℝ → ℂ} (hW : IsTestWeight W) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin W s‖ ≤ C := by
  let B : ℝ → ℝ := fun y =>
    ‖(y : ℂ) ^ ((a : ℂ) - 1) * W y‖ + ‖(y : ℂ) ^ ((b : ℂ) - 1) * W y‖
  have ha := CompactMellin.compact_weight_mellin_convergent W hW.1 hW.vanishes (a : ℂ)
  have hb := CompactMellin.compact_weight_mellin_convergent W hW.1 hW.vanishes (b : ℂ)
  have hB : IntegrableOn B (Ioi 0) := ha.norm.add hb.norm
  refine ⟨∫ y in Ioi 0, B y,
    integral_nonneg (fun y => add_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0 < y at hy
  have hp := rpow_between_endpoints y (a - 1) (b - 1) (s.re - 1) hy (by linarith) (by linarith)
  change ‖(y : ℂ) ^ (s - 1) * W y‖ ≤ B y
  dsimp only [B]
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (W y))

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.mellin_eq_mellinSchwartz
#print axioms Vinogradov.Mobius.mellin_polynomial_weight_integrable
