import Vinogradov.Mobius.CompactMellin
import Vinogradov.Mobius.TestWeight

/-!
# The converse smoothed Mobius criterion

This file states the actual twisted Mobius sum in Mathlib definitions. Its
only cancellation hypothesis is the power bound to which the converse applies.
The forward bound is a separate obligation, not assumed to have been proved by
this criterion. Generic helper provenance is retained in the adjacent files.
-/

noncomputable section
namespace Vinogradov.Mobius

open Filter Asymptotics MeasureTheory Set Complex Metric
open scoped Topology Classical LSeries.notation ArithmeticFunction.Moebius

def IsTestWeight (W : ℝ → ℂ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) W ∧ tsupport W ⊆ Ioo 1 2

def coefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * (ArithmeticFunction.moebius n : ℂ)

def scaledSum {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, coefficient χ n * W ((n : ℝ) * t)

def smoothedSum {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  scaledSum χ W X⁻¹

theorem coefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) : coefficient χ 0 = 0 := by
  simp [coefficient]

theorem IsTestWeight.vanishes {W : ℝ → ℂ} (hW : IsTestWeight W)
    (y : ℝ) (hy : y ≤ 1 ∨ 2 ≤ y) : W y = 0 := by
  by_contra hne
  have hs : y ∈ Function.support W := hne
  have hts : y ∈ tsupport W := subset_closure hs
  have hh := hW.2 hts
  rcases hy with hy | hy <;> linarith [hh.1, hh.2]

theorem scaledSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => coefficient χ n * W ((n : ℝ) * t)) (scaledSum χ W t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
  have hNmul : 2 < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
  have htail (n : ℕ) (hn : n ∉ Finset.range N) :
      coefficient χ n * W ((n : ℝ) * t) = 0 := by
    have hnn : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hnn
    have hnprod : 2 ≤ (n : ℝ) * t :=
      hNmul.le.trans (mul_le_mul_of_nonneg_right hnr ht.le)
    simp [hsupp _ hnprod]
  exact (hasSum_sum_of_ne_finset_zero htail).summable.hasSum

theorem coefficient_LSeriesSummable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (coefficient χ) s := by
  exact χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

theorem coefficient_euler_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s * LSeries (coefficient χ) s = 1 := by
  rw [χ.LFunction_eq_LSeries hs]
  exact χ.LSeries.mul_mu_eq_one hs

theorem smoothed_mellin_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {W : ℝ → ℂ} (hW : IsTestWeight W)
    {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s * mellin (smoothedSum χ W) (-s) = mellin W s := by
  have hsupp := hW.vanishes
  have hF := fun t ht => scaledSum_hasSum χ W (fun y hy => hsupp y (Or.inr hy)) ht
  have hconv := CompactMellin.compact_weight_mellin_convergent W hW.1 hsupp s
  have hls := coefficient_LSeriesSummable χ hs
  have hM := CompactMellin.mellin_weighted_sum (coefficient χ) W (scaledSum χ W) s
    (coefficient_zero χ) hF
    (CompactMellin.weighted_term_integrable (coefficient χ) (coefficient_zero χ) W s hconv)
    (CompactMellin.weighted_terms_fubini (coefficient χ) (coefficient_zero χ) W s hls) hls
  change χ.LFunction s * mellin (fun X => scaledSum χ W X⁻¹) (-s) = _
  rw [hM]
  calc
    χ.LFunction s * (mellin W s * LSeries (coefficient χ) s) =
        (χ.LFunction s * LSeries (coefficient χ) s) * mellin W s := by ring
    _ = mellin W s := by rw [coefficient_euler_identity χ hs, one_mul]

theorem nonvanishing_of_one_smoothed_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {W : ℝ → ℂ} (hW : IsTestWeight W)
    {σ : ℝ} (hσ : σ < 1)
    (hbound : smoothedSum χ W =O[atTop] (fun X : ℝ => X ^ σ))
    {ρ : ℂ} (hρ : σ < ρ.re) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hsupp := hW.vanishes
  have hF := fun t ht => scaledSum_hasSum χ W (fun y hy => hsupp y (Or.inr hy)) ht
  have hlocal : LocallyIntegrableOn (smoothedSum χ W) (Ioi 0) :=
    CompactMellin.weighted_sum_inv_locallyIntegrableOn_pos (coefficient χ) W
      (scaledSum χ W) hW.1 (fun y hy => hsupp y (Or.inr hy)) hF
  have hzero : smoothedSum χ W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) :=
    CompactMellin.weighted_sum_zero_near_small_D (coefficient χ) (coefficient_zero χ)
      W (scaledSum χ W) (fun y hy => hsupp y (Or.inr hy)) hF
  have hM : AnalyticOnNhd ℂ (fun s : ℂ => mellin (smoothedSum χ W) (-s)) U :=
    CompactMellin.inverse_mellin_analytic (smoothedSum χ W) σ hlocal hbound hzero
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hWa : AnalyticOnNhd ℂ (mellin W) U :=
    CompactMellin.compact_weight_mellin_analytic W hW.1 hsupp σ
  have htwo : (2 : ℂ) ∈ U := by change σ < (2 : ℂ).re; norm_num; linarith
  have hevent : (fun s : ℂ => χ.LFunction s * mellin (smoothedSum χ W) (-s))
      =ᶠ[𝓝 (2 : ℂ)] mellin W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num :
      (2 : ℂ) ∈ {s : ℂ | 1 < s.re}))] with s hs
    exact smoothed_mellin_identity χ hW hs
  have hid := (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hWa
    ((convex_halfSpace_re_gt σ).isPreconnected) htwo hevent
  intro hzeroL
  have heqρ := hid hρ
  change χ.LFunction ρ * mellin (smoothedSum χ W) (-ρ) = mellin W ρ at heqρ
  rw [hzeroL, zero_mul] at heqρ
  exact hWρ heqρ.symm

theorem explicit_test_weight (ρ : ℂ) : IsTestWeight (TestWeight.weight ρ) := by
  refine ⟨TestWeight.weight_smooth ρ, ?_⟩
  have hsubset : tsupport (TestWeight.weight ρ) ⊆ closedBall (3 / 2 : ℝ) (1 / 4) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro y hy
    by_contra hnot
    have hd : (1 / 4 : ℝ) ≤ dist y (3 / 2) :=
      (lt_of_not_ge (by simpa only [mem_closedBall] using hnot)).le
    have hb : TestWeight.bump y = 0 := TestWeight.bumpData.zero_of_le_dist hd
    exact hy (by simp [TestWeight.weight, hb])
  intro y hy
  have hd := hsubset hy
  rw [mem_closedBall, Real.dist_eq] at hd
  have hh := abs_le.mp hd
  constructor <;> linarith [hh.1, hh.2]

/-- The reverse implication in the appendix, with all weights and the actual
twisted Mobius coefficients quantified explicitly. -/
theorem nonvanishing_of_smoothed_mobius_cancellation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ : ℝ} (hθ : θ < 1)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ W : ℝ → ℂ, IsTestWeight W →
      smoothedSum χ W =O[atTop] (fun X : ℝ => X ^ (θ + ε)))
    {ρ : ℂ} (hρ : θ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  let σ : ℝ := min ((θ + ρ.re) / 2) ((θ + 1) / 2)
  have hσθ : θ < σ := by
    apply lt_min <;> linarith
  have hσρ : σ < ρ.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hσ1 : σ < 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb := hbound (σ - θ) (sub_pos.mpr hσθ) (TestWeight.weight ρ) (explicit_test_weight ρ)
  have hb' : smoothedSum χ (TestWeight.weight ρ) =O[atTop] (fun X : ℝ => X ^ σ) := by
    simpa only [add_sub_cancel] using hb
  exact nonvanishing_of_one_smoothed_bound χ hχ (explicit_test_weight ρ) hσ1 hb'
    hσρ (TestWeight.weight_mellin_ne_zero ρ)

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.smoothed_mellin_identity
#print axioms Vinogradov.Mobius.nonvanishing_of_one_smoothed_bound
#print axioms Vinogradov.Mobius.explicit_test_weight
#print axioms Vinogradov.Mobius.nonvanishing_of_smoothed_mobius_cancellation
