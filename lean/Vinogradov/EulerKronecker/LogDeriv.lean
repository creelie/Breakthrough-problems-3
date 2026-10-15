import Mathlib
import Vinogradov.Analytic
import Vinogradov.Main
import Vinogradov.EulerKronecker.Mellin

/-!
# The logarithmic derivative of `L(s, χ)` at `s = 1`

If no `L(s, χ)` with `χ` nonprincipal vanishes on `re s > 7/8`, then
`|L'/L(1, χ)| ≤ C log log (q + 2)` for every nonprincipal character `χ` modulo `q`.
-/

namespace Vinogradov.EulerKronecker

open Complex Real Set MeasureTheory Filter Topology Asymptotics
open Vinogradov.Riesz
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- The Mellin integral at `-1` of a Riesz sum bounded by `c x` up to `Y` and by `M x^θ`
beyond `Y`. -/
theorem norm_mellin_rieszSum_le (a : ℕ → ℂ) {c M θ Y : ℝ} (hθ : θ < 1) (hY : 1 ≤ Y)
    (hc : 0 ≤ c) (hM : 0 ≤ M)
    (h1 : ∀ x : ℝ, 1 ≤ x → x ≤ Y → ‖rieszSum a x‖ ≤ c * x)
    (h2 : ∀ x : ℝ, Y < x → ‖rieszSum a x‖ ≤ M * x ^ θ) :
    ‖mellin (rieszSum a) (-1)‖ ≤ c * Real.log Y + M * Y ^ (θ - 1) / (1 - θ) := by
  have hY0 : 0 < Y := by linarith
  set g1 : ℝ → ℝ := (Icc 1 Y).indicator (fun t => c * t⁻¹) with hg1def
  set g2 : ℝ → ℝ := (Ioi Y).indicator (fun t => M * t ^ (θ - 2)) with hg2def
  have hg1 : IntegrableOn (fun t : ℝ => c * t⁻¹) (Icc 1 Y) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.mul (continuousOn_inv₀.mono (fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]))
  have hg2 : IntegrableOn (fun t : ℝ => M * t ^ (θ - 2)) (Ioi Y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hY0).const_mul M
  have i1 : Integrable g1 := (integrable_indicator_iff measurableSet_Icc).mpr hg1
  have i2 : Integrable g2 := (integrable_indicator_iff measurableSet_Ioi).mpr hg2
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ ((-1 : ℂ) - 1) • rieszSum a t‖ ≤ g1 t + g2 t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : ((-1 : ℂ) - 1).re = -2 := by norm_num
    rw [hre]
    have hi1 : 0 ≤ g1 t := indicator_nonneg (fun t ht =>
      mul_nonneg hc (inv_nonneg.mpr (by linarith [ht.1]))) t
    have hi2 : 0 ≤ g2 t := indicator_nonneg (fun t ht =>
      mul_nonneg hM (Real.rpow_nonneg (by have : Y < t := ht; linarith) _)) t
    have hp : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    by_cases ht1 : t < 1
    · rw [rieszSum_eq_zero_of_lt_one a ht1, norm_zero, mul_zero]
      exact add_nonneg hi1 hi2
    · push Not at ht1
      by_cases htY : t ≤ Y
      · have hm : t ∈ Icc 1 Y := ⟨ht1, htY⟩
        have hg1t : g1 t = c * t⁻¹ := by rw [hg1def, indicator_of_mem hm]
        rw [hg1t]
        calc t ^ (-2 : ℝ) * ‖rieszSum a t‖ ≤ t ^ (-2 : ℝ) * (c * t) := by
              gcongr; exact h1 t ht1 htY
          _ = c * t⁻¹ := by
              rw [Real.rpow_neg ht0.le, Real.rpow_two]; field_simp
          _ ≤ c * t⁻¹ + g2 t := le_add_of_nonneg_right hi2
      · push Not at htY
        have hm : t ∈ Ioi Y := htY
        have hm' : t ∉ Icc 1 Y := fun h => by linarith [h.2]
        have hg1t : g1 t = 0 := by rw [hg1def, indicator_of_notMem hm']
        have hg2t : g2 t = M * t ^ (θ - 2) := by rw [hg2def, indicator_of_mem hm]
        rw [hg1t, hg2t, zero_add]
        calc t ^ (-2 : ℝ) * ‖rieszSum a t‖ ≤ t ^ (-2 : ℝ) * (M * t ^ θ) := by
              gcongr; exact h2 t htY
          _ = M * t ^ (θ - 2) := by
              rw [mul_left_comm, ← Real.rpow_add ht0]; ring_nf
  have hint1 : ∫ t in Ioi (0 : ℝ), g1 t = c * Real.log Y := by
    have hsub : Icc 1 Y ⊆ Ioi (0 : ℝ) := fun t ht => show (0 : ℝ) < t by linarith [ht.1]
    rw [hg1def, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY,
      intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hY0, div_one]
  have hint2 : ∫ t in Ioi (0 : ℝ), g2 t = M * Y ^ (θ - 1) / (1 - θ) := by
    rw [hg2def, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi hY0.le), integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hY0]
    have h3 : θ - 2 + 1 = θ - 1 := by ring
    rw [h3, neg_div, ← div_neg, neg_sub, mul_div_assoc]
  calc ‖mellin (rieszSum a) (-1)‖
      ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((-1 : ℂ) - 1) • rieszSum a t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), (g1 t + g2 t) := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall (fun _ => norm_nonneg _)
        · exact (i1.add i2).restrict
        · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt)
    _ = c * Real.log Y + M * Y ^ (θ - 1) / (1 - θ) := by
        rw [integral_add i1.restrict i2.restrict, hint1, hint2]

/-- The Riesz sum of `χ Λ` is at most `ψ(x)`. -/
lemma norm_rieszSum_le_psi {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖rieszSum (↗χ * ↗Λ) x‖ ≤ Chebyshev.psi x := by
  unfold rieszSum Chebyshev.psi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnx' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnx
  have h01 : ‖(1 : ℂ) - (n : ℂ) / (x : ℂ)‖ ≤ 1 := by
    rw [show (1 : ℂ) - (n : ℂ) / (x : ℂ) = ((1 - n / x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg]
    · have : 0 ≤ (n : ℝ) / x := by positivity
      linarith
    · rw [sub_nonneg, div_le_one hx]; exact hnx'
  simp only [Pi.mul_apply, norm_mul]
  have hχn : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hΛ : ‖((Λ n : ℝ) : ℂ)‖ = Λ n := by
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hΛ]
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  calc ‖χ ↑n‖ * Λ n * ‖1 - (n : ℂ) / (x : ℂ)‖ ≤ 1 * Λ n * 1 := by gcongr
    _ = Λ n := by ring

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The exponent `θ` of the Riesz-sum bound. -/
noncomputable def θ0 : ℝ := 7 / 8 + 3 / 1000

/-- Under the zero-free half-plane, the Riesz sums of `χ Λ` are `≤ K x^{θ0} log (q + 2)`. -/
theorem riesz_bound_of_zeroFree (hZ : Main.ZeroFree) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ θ0 * Real.log (q + 2) := by
  obtain ⟨K, hK, hKb⟩ := Analytic.riesz_character_bound (e := 1 / 2000) (by norm_num) (by norm_num)
  refine ⟨K, hK, fun q _ χ hχ x hx => ?_⟩
  have h := hKb q χ hχ (7 / 8 - 1 / 1000) (by norm_num) (by norm_num)
    (fun z hz => hZ q χ hχ z (by linarith)) x hx
  have he : (7 / 8 - 1 / 1000 : ℝ) + 8 * (1 / 2000) = θ0 := by unfold θ0; norm_num
  rwa [he] at h

/-- **Theorem (A).** Under the zero-free half-plane, `|L'/L(1, χ)| ≤ C log log (q + 2)` for every
nonprincipal character `χ` modulo `q`. -/
theorem logDeriv_one_le_of_zeroFree (hZ : Main.ZeroFree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        C * Real.log (Real.log (q + 2)) := by
  obtain ⟨K, hK, hKb⟩ := riesz_bound_of_zeroFree hZ
  have hθ : θ0 < 1 := by unfold θ0; norm_num
  have h1θ : 0 < 1 - θ0 := by linarith
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : 0 < c := by positivity
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos one_lt_log_three
  refine ⟨2 * c / (1 - θ0) + 2 * K / ((1 - θ0) * Real.log (Real.log 3)), by positivity, ?_⟩
  intro q _ χ hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Lq : ℝ := Real.log (q + 2) with hLq
  have hLq3 : Real.log 3 ≤ Lq := Real.log_le_log (by norm_num) (by linarith)
  have hLq1 : 1 < Lq := lt_of_lt_of_le one_lt_log_three hLq3
  have hLq0 : 0 < Lq := by linarith
  set Y : ℝ := Lq ^ (1 / (1 - θ0)) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hLq1.le (by positivity)
  have hR := neg_logDeriv_one_eq χ hχ (K := K * Lq) hθ (fun x hx => by
    have := hKb q χ hχ x hx; linarith [this])
  have hM := norm_mellin_rieszSum_le (↗χ * ↗Λ) (c := c) (M := K * Lq) hθ hY1 hc0.le
    (by positivity)
    (fun x hx _ => (norm_rieszSum_le_psi χ (by linarith)).trans
      (Chebyshev.psi_le_const_mul_self (by linarith)))
    (fun x hx => by have := hKb q χ hχ x (by linarith); linarith [this])
  have hlogY : Real.log Y = 1 / (1 - θ0) * Real.log Lq := Real.log_rpow hLq0 _
  have hYpow : Y ^ (θ0 - 1) = Lq⁻¹ := by
    rw [hY, ← Real.rpow_mul hLq0.le]
    have : 1 / (1 - θ0) * (θ0 - 1) = -1 := by field_simp; ring
    rw [this, Real.rpow_neg_one]
  rw [hlogY, hYpow] at hM
  have hLL : Real.log (Real.log 3) ≤ Real.log Lq :=
    Real.log_le_log (by linarith [one_lt_log_three]) hLq3
  have hnorm : ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ =
      2 * ‖mellin (rieszSum (↗χ * ↗Λ)) (-1)‖ := by
    rw [← norm_neg, ← neg_div, hR, norm_mul]; norm_num
  rw [hnorm]
  have hKL : K * Lq * Lq⁻¹ / (1 - θ0) = K / (1 - θ0) := by field_simp
  rw [hKL] at hM
  have hK2 : 2 * (K / (1 - θ0)) ≤
      2 * K / ((1 - θ0) * Real.log (Real.log 3)) * Real.log Lq := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 2 * (K / (1 - θ0)) * ((1 - θ0) * Real.log (Real.log 3)) =
        2 * K * Real.log (Real.log 3) := by field_simp
    rw [this]
    gcongr
  calc 2 * ‖mellin (rieszSum (↗χ * ↗Λ)) (-1)‖
      ≤ 2 * (c * (1 / (1 - θ0) * Real.log Lq) + K / (1 - θ0)) := by gcongr
    _ = 2 * c / (1 - θ0) * Real.log Lq + 2 * (K / (1 - θ0)) := by ring
    _ ≤ 2 * c / (1 - θ0) * Real.log Lq +
          2 * K / ((1 - θ0) * Real.log (Real.log 3)) * Real.log Lq := by gcongr
    _ = (2 * c / (1 - θ0) + 2 * K / ((1 - θ0) * Real.log (Real.log 3))) * Real.log Lq := by ring

end Vinogradov.EulerKronecker
