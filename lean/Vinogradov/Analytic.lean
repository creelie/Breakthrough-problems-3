import Mathlib
import OAI.NumberTheory.DirichletL.LogarithmicControl
import Vinogradov.MRT
import Vinogradov.Riesz
import Vinogradov.EulerLog
import Vinogradov.ContourShift

/-!
# Riesz-weighted prime sums of a nonprincipal character under a zero-free half-plane

Let `χ` be a nonprincipal Dirichlet character modulo `q`, and suppose that `L(s, χ)` has no
zero with `re s > a + 2e`. Then
`‖∑_{n ≤ x} χ(n) Λ(n) (1 - n/x)‖ ≤ K x^{a + 8e} log (q + 2)` for `x ≥ 1`,
with `K` depending only on `e`.

The logarithmic derivative is bounded on `re s ≥ a + 8e` by the logarithmic control lemma
`OAI.SevenEighths.LogarithmicControl.logarithmic_control`, and the Riesz sum is the inverse
Mellin transform of `-L'/L(s) / (s (s + 1))`, moved from `re s = 2` to `re s = a + 8e`.
-/

namespace Vinogradov.Analytic

open Complex Set Metric Filter MeasureTheory
open scoped Topology ArithmeticFunction.vonMangoldt LSeries.notation

/-- Points of a disk of radius `< 3/2` about `2 + t i` have norm at most `4 + |t|`. -/
theorem norm_le_of_mem_ball {t r : ℝ} {z : ℂ} (hr : r ≤ 3 / 2)
    (hz : z ∈ ball (2 + (t : ℂ) * I) r) : ‖z‖ ≤ 4 + |t| := by
  have hn : ‖z - (2 + (t : ℂ) * I)‖ < r := by simpa [mem_ball, dist_eq_norm] using hz
  have hc : ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ 2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  calc ‖z‖ = ‖(z - (2 + (t : ℂ) * I)) + (2 + (t : ℂ) * I)‖ := by ring_nf
    _ ≤ ‖z - (2 + (t : ℂ) * I)‖ + ‖(2 : ℂ) + (t : ℂ) * I‖ := norm_add_le _ _
    _ ≤ 4 + |t| := by linarith

/-- The bound for the logarithmic derivative of `L(s, χ)` to the right of a zero-free
half-plane. -/
theorem logDeriv_bound {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      (∀ z : ℂ, a + 2 * e < z.re → DirichletCharacter.LFunction χ z ≠ 0) →
      ∀ σ t : ℝ, a + 8 * e ≤ σ → σ ≤ 2 →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I) /
            DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          K * Real.log (2 * q * (3 + |t|) ^ 2) := by
  obtain ⟨D, -, hctrl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := EulerLog.eulerLogBound) (M := 1) (ε := 1) he he'
    EulerLog.eulerLogBound_ge_one le_rfl one_pos
  have hO := OAI.SevenEighths.LogarithmicControl.outerConstant_ge_one he he'
    EulerLog.eulerLogBound_ge_one (le_refl (1 : ℝ))
  refine ⟨OAI.SevenEighths.LogarithmicControl.outerConstant e EulerLog.eulerLogBound 1 /
    (2 * e), by positivity, ?_⟩
  intro q _ χ hχ a ha ha' hzero σ t hσ hσ'
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hC := OAI.SevenEighths.LogarithmicControl.conductor_height_scale_ge_exp (q : ℝ) t hq
  obtain ⟨hEd, hEe, hEb⟩ := EulerLog.eulerLog_inner_disk χ t
  have hres := hctrl a (2 * q * (3 + |t|) ^ 2) (DirichletCharacter.LFunction χ)
    (EulerLog.eulerLog χ) (2 + (t : ℂ) * I) ha ha' hC
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn)
    (fun z hz => hzero z (OAI.SevenEighths.LogarithmicControl.disk_re_gt hz))
    (fun z hz => by
      have hz2 : z ∈ ball (2 + (t : ℂ) * I) (2 - a - 2 * e) :=
        ball_subset_ball (by linarith) hz
      have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hz2
      have hn := norm_le_of_mem_ball (by linarith) hz
      have hL := MRT.mrt_character_LFunction_norm_halfPlane χ hχ (s := z) (by linarith)
      rw [Real.rpow_one]
      have h1 : (4 + |t|) ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
      calc ‖DirichletCharacter.LFunction χ z‖ ≤ (2 * q : ℝ) * ‖z‖ := hL
        _ ≤ (2 * q : ℝ) * (4 + |t|) := by gcongr
        _ ≤ 2 * q * (3 + |t|) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity))
    hEd hEe hEb
  exact hres.2 _ (OAI.SevenEighths.LogarithmicControl.same_height_mem_disk le_rfl hσ hσ')

/-- `log (2 q (3 + |t|)^2) ≤ 10 log (q + 2) (1 + |t|)^{1/2}`. -/
theorem log_scale_le {q : ℕ} (hq : (1 : ℝ) ≤ q) (t : ℝ) :
    Real.log (2 * q * (3 + |t|) ^ 2) ≤ 10 * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hu1 : (1 : ℝ) ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlq : 1 ≤ Real.log (q + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.log (2 * q) ≤ 2 * Real.log (q + 2) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [show ((q : ℝ) + 2) ^ (2 : ℝ) = ((q : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
    nlinarith
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : Real.log (3 + |t|) ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by
    have hl := Real.log_le_rpow_div (x := 3 + |t|) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    have hm : (3 + |t|) ^ (1 / 2 : ℝ) ≤ (4 * (1 + |t|)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity), h4] at hm
    calc Real.log (3 + |t|) ≤ (3 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) := hl
      _ ≤ 2 * (1 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) := by gcongr
      _ = 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by ring
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  nlinarith

/-- `‖s (s + 1)‖ ≥ (1 + |t|)^2 / 8` for `s = σ + t i` with `σ ≥ 1/2`. -/
theorem denominator_ge {σ t : ℝ} (hσ : 1 / 2 ≤ σ) :
    (1 + |t|) ^ 2 / 8 ≤ ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)‖ := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hre : z.re = σ := by simp [z]
  have him : z.im = t := by simp [z]
  have h1 : |t| ≤ ‖z‖ := him ▸ Complex.abs_im_le_norm z
  have h2 : σ ≤ ‖z‖ := hre ▸ Complex.re_le_norm z
  have h3 : |t| ≤ ‖z + 1‖ := by
    have := Complex.abs_im_le_norm (z + 1)
    simpa [him] using this
  have h4 : σ + 1 ≤ ‖z + 1‖ := by
    have := Complex.re_le_norm (z + 1)
    simpa [hre] using this
  have ha : (1 + |t|) / 4 ≤ ‖z‖ := by linarith
  have hb : (1 + |t|) / 2 ≤ ‖z + 1‖ := by linarith
  rw [norm_mul]
  have := mul_le_mul ha hb (by positivity) (norm_nonneg _)
  nlinarith

/-- The integrand of the inverse Mellin transform, `x^s (-L'/L)(s) / (s (s + 1))`. -/
noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (z : ℂ) :
    ℂ :=
  ((1 / x : ℝ) : ℂ) ^ (-z) *
    (-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z /
      (z * (z + 1)))

theorem integrand_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x K : ℝ}
    (hx : 0 < x) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hq : (1 : ℝ) ≤ q) (hK : 0 ≤ K)
    (hB : ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      K * Real.log (2 * q * (3 + |t|) ^ 2)) :
    ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      80 * K * Real.log (q + 2) * x ^ σ * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
  have ht : 0 < 1 + |t| := by positivity
  have hlq : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  have hden := denominator_ge (t := t) hσ
  have hdpos : 0 < ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)‖ :=
    lt_of_lt_of_le (by positivity) hden
  have hpow : ‖((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  have hsplit : (1 + |t|) ^ (-(3 / 2 : ℝ)) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
    rw [show (-(3 / 2 : ℝ)) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub ht,
      Real.rpow_natCast]
  have hlog := log_scale_le hq t
  unfold integrand
  rw [norm_mul, hpow, norm_div, neg_div, norm_neg]
  rw [hsplit]
  have hnum : ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      10 * K * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ) := by
    calc _ ≤ K * Real.log (2 * q * (3 + |t|) ^ 2) := hB
      _ ≤ K * (10 * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hK
      _ = _ := by ring
  have hxσ : 0 ≤ x ^ σ := by positivity
  calc x ^ σ * (‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ /
        ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)‖)
      ≤ x ^ σ * (10 * K * Real.log (q + 2) * (1 + |t|) ^ (1 / 2 : ℝ) /
          ((1 + |t|) ^ 2 / 8)) := by
        gcongr
    _ = 80 * K * Real.log (q + 2) * x ^ σ * ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2) := by
        field_simp
        ring

theorem integrand_differentiableAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re)
    (hL : DirichletCharacter.LFunction χ z ≠ 0) :
    DifferentiableAt ℂ (integrand χ x) z := by
  have hc : ((1 / x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.mpr hx).ne'
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hdd : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) z :=
    (hLd.differentiableOn.deriv isOpen_univ).differentiableAt
      (isOpen_univ.mem_nhds (mem_univ z))
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have h' : (z + 1).re = 0 := by rw [h]; simp
    simp at h'
    linarith
  change DifferentiableAt ℂ (fun w => ((1 / x : ℝ) : ℂ) ^ (-w) *
    (-deriv (DirichletCharacter.LFunction χ) w / DirichletCharacter.LFunction χ w /
      (w * (w + 1)))) z
  apply DifferentiableAt.mul
  · exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hc)
  · apply DifferentiableAt.div
    · exact (hdd.neg).div (hLd z) hL
    · exact differentiableAt_id.mul (differentiableAt_id.add_const 1)
    · exact mul_ne_zero hz0 hz1

/-- **The character sum estimate.** If `L(s, χ)` has no zero with `re s > a + 2e`, then the
Riesz-weighted prime sum of the nonprincipal character `χ` is at most
`K x^{a + 8e} log (q + 2)`, with `K` depending only on `e`. -/
theorem riesz_character_bound {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      (∀ z : ℂ, a + 2 * e < z.re → DirichletCharacter.LFunction χ z ≠ 0) →
      ∀ x : ℝ, 1 ≤ x →
        ‖Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ (a + 8 * e) * Real.log (q + 2) := by
  obtain ⟨K0, hK0, hK0b⟩ := logDeriv_bound he he'
  set I0 : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2 : ℝ)) with hI0def
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-(3 / 2 : ℝ))) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2)
      (by rw [Module.finrank_self]; norm_num)
    simpa only [Real.norm_eq_abs] using h
  have hI0 : 0 ≤ I0 := integral_nonneg (fun t => by positivity)
  refine ⟨80 * K0 * I0 / (2 * Real.pi) + 1, by positivity, ?_⟩
  intro q _ χ hχ a ha ha' hzero x hx
  have hx0 : 0 < x := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  set σ0 := a + 8 * e with hσ0
  have hσ0' : σ0 ≤ 2 := by linarith
  have hpt : ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 2 → ∀ t : ℝ,
      ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        80 * K0 * Real.log (q + 2) * x ^ σ * (1 + |t|) ^ (-(3 / 2 : ℝ)) :=
    fun σ h1 h2 t => integrand_norm_le χ hx0 (by linarith) hq hK0.le
      (hK0b q χ hχ a ha ha' hzero σ t h1 h2)
  have hdiff : ∀ z : ℂ, σ0 ≤ z.re → z.re ≤ 2 → DifferentiableAt ℂ (integrand χ x) z :=
    fun z h1 _ => integrand_differentiableAt χ hχ hx0 (by linarith) (hzero z (by linarith))
  have hcont : ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 2 →
      Continuous (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.comp (g := integrand χ x)
    · exact (hdiff _ (by simpa using h1) (by simpa using h2)).continuousAt
    · fun_prop
  have hint : ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    refine Integrable.mono' (hI.const_mul (80 * K0 * Real.log (q + 2) * x ^ σ))
      (hcont σ h1 h2).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun t => hpt σ h1 h2 t)
  have hgrowth : ∀ σ ∈ Icc σ0 2, ∀ t : ℝ,
      ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        (80 * K0 * Real.log (q + 2) * x ^ (2 : ℝ)) * Real.exp (0 * |t|) := by
    intro σ hσ t
    rw [zero_mul, Real.exp_zero, mul_one]
    refine (hpt σ hσ.1 hσ.2 t).trans ?_
    have h1 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have h2 : (1 + |t|) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have h3 : 0 ≤ 80 * K0 * Real.log (q + 2) := by positivity
    have h4 : 0 ≤ (1 + |t|) ^ (-(3 / 2 : ℝ)) := by positivity
    calc 80 * K0 * Real.log (q + 2) * x ^ σ * (1 + |t|) ^ (-(3 / 2 : ℝ))
        ≤ 80 * K0 * Real.log (q + 2) * x ^ (2 : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 h4 (by positivity)
      _ = _ := by ring
  have hshift := ContourShift.integral_eq_of_exponential_strip_growth (integrand χ x) σ0 2 0
    (80 * K0 * Real.log (q + 2) * x ^ (2 : ℝ)) hσ0' le_rfl (by positivity) hdiff
    (hint σ0 le_rfl hσ0') (hint 2 hσ0' le_rfl) hgrowth
  have hsum : LSeriesSummable (↗χ * ↗Λ) ((2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simp)
  have hR := Riesz.rieszSum_mellinInv (σ := 2) (by norm_num) hx0 (↗χ * ↗Λ) hsum
  have hline : mellinInv 2 (fun s => LSeries (↗χ * ↗Λ) s / (s * (s + 1))) (1 / x) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, integrand χ x (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall (fun t => ?_)
    have hre : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by simp
    simp only [integrand, smul_eq_mul]
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hre,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hre,
      ← DirichletCharacter.LFunction_eq_LSeries χ hre]
  rw [← hR, hline, ← hshift, norm_smul]
  have hbound : ‖∫ t : ℝ, integrand χ x ((σ0 : ℂ) + (t : ℂ) * I)‖ ≤
      80 * K0 * Real.log (q + 2) * x ^ σ0 * I0 := by
    rw [hI0def, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hI.const_mul _)
      (Eventually.of_forall (fun t => hpt σ0 le_rfl hσ0' t))
  have hpi : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hxs : 0 ≤ x ^ σ0 := by positivity
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, integrand χ x ((σ0 : ℂ) + (t : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * (80 * K0 * Real.log (q + 2) * x ^ σ0 * I0) := by
        gcongr
    _ = 80 * K0 * I0 / (2 * Real.pi) * x ^ σ0 * Real.log (q + 2) := by ring
    _ ≤ (80 * K0 * I0 / (2 * Real.pi) + 1) * x ^ σ0 * Real.log (q + 2) := by
        have : 0 ≤ x ^ σ0 * Real.log (q + 2) := by positivity
        nlinarith

end Vinogradov.Analytic
