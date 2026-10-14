import Vinogradov.Analytic
import Vinogradov.Final

/-!
# The Lindelöf bound and character sums to the right of a zero-free half-plane

Let `χ` be a nonprincipal Dirichlet character modulo `q`, and suppose that `L(s, χ)` has no
zero with `re s > a + 2e`. Then for every `ε > 0`

* `‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ D (2 q (3 + |t|)^2)^ε` for `a + 8e ≤ re s ≤ 2`, `t = im s`;
* `‖∑_{n ≤ x} χ(n)‖ ≤ K q^ε x^{a + 8e + 4ε}` for `x ≥ 1`,

with `D` and `K` depending only on `e` and `ε`. The first bound is the first part of the
logarithmic control lemma `OAI.SevenEighths.LogarithmicControl.logarithmic_control`. For the
second, the Riesz means `y R(y) = ∑_{n ≤ y} χ(n) (y - n)` are inverse Mellin transforms of
`L(s, χ) / (s (s + 1))`, moved from `re s = 2` to `re s = a + 8e`; the difference
`(x + h) R(x + h) - x R(x)` has the kernel `((x + h)^{s+1} - x^{s+1}) / (s (s + 1))`, and
`h ∑_{n ≤ x} χ(n)` differs from it by at most `h (h + 1)`.

With the zero-free half-plane `re s > 7/8` these give `lindelof`, `character_sum_bound` and
`character_sum_le_rpow`.
-/

namespace Vinogradov.CharSum

open Complex Set Metric Filter MeasureTheory
open scoped LSeries.notation

/-- **Lindelöf bound.** The values of `L(s, χ)` and of `L(s, χ)⁻¹` to the right of a zero-free
half-plane. -/
theorem norm_bound {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      (∀ z : ℂ, a + 2 * e < z.re → DirichletCharacter.LFunction χ z ≠ 0) →
      ∀ σ t : ℝ, a + 8 * e ≤ σ → σ ≤ 2 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ +
          ‖(DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
          D * (2 * q * (3 + |t|) ^ 2) ^ ε := by
  obtain ⟨D, hD, hctrl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := EulerLog.eulerLogBound) (M := 1) (ε := ε) he he'
    EulerLog.eulerLogBound_ge_one le_rfl hε
  refine ⟨D, hD, ?_⟩
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
      have hn := Analytic.norm_le_of_mem_ball (by linarith) hz
      have hL := MRT.mrt_character_LFunction_norm_halfPlane χ hχ (s := z) (by linarith)
      rw [Real.rpow_one]
      have h1 : (4 + |t|) ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
      calc ‖DirichletCharacter.LFunction χ z‖ ≤ (2 * q : ℝ) * ‖z‖ := hL
        _ ≤ (2 * q : ℝ) * (4 + |t|) := by gcongr
        _ ≤ 2 * q * (3 + |t|) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity))
    hEd hEe hEb
  exact hres.1 _ (closedBall_subset_closedBall (by linarith)
    (OAI.SevenEighths.LogarithmicControl.same_height_mem_disk le_rfl hσ hσ'))

/-- `(2 q (3 + |t|)^2)^ε ≤ (18 q)^ε (1 + |t|)^{2ε}`. -/
theorem scale_le (q : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (2 * q * (3 + |t|) ^ 2) ^ ε ≤ (18 * q) ^ ε * (1 + |t|) ^ (2 * ε) := by
  have h0 : (3 + |t|) ^ 2 ≤ 9 * (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : 2 * (q : ℝ) * (3 + |t|) ^ 2 ≤ 18 * q * (1 + |t|) ^ 2 := by nlinarith
  calc (2 * q * (3 + |t|) ^ 2) ^ ε ≤ (18 * q * (1 + |t|) ^ 2) ^ ε :=
        Real.rpow_le_rpow (by positivity) h1 hε
    _ = (18 * q) ^ ε * (1 + |t|) ^ (2 * ε) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_two,
          ← Real.rpow_mul (by positivity)]

/-- The integrand `x^z L(z, χ) / (z (z + 1))`. -/
noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (z : ℂ) :
    ℂ :=
  ((1 / x : ℝ) : ℂ) ^ (-z) * (DirichletCharacter.LFunction χ z / (z * (z + 1)))

theorem integrand_differentiableAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (integrand χ x) z := by
  have hc : ((1 / x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.mpr hx).ne'
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have h' : (z + 1).re = 0 := by rw [h]; simp
    simp at h'
    linarith
  change DifferentiableAt ℂ (fun w => ((1 / x : ℝ) : ℂ) ^ (-w) *
    (DirichletCharacter.LFunction χ w / (w * (w + 1)))) z
  apply DifferentiableAt.mul
  · exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hc)
  · exact (hLd z).div (differentiableAt_id.mul (differentiableAt_id.add_const 1))
      (mul_ne_zero hz0 hz1)

/-- `‖L(s, χ) / (s (s + 1))‖ ≤ 8 D (18 q)^ε (1 + |t|)^{-(2 - 2ε)}`. -/
theorem quotient_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {D ε σ t : ℝ}
    (hσ : 1 / 2 ≤ σ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hB : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I) /
        (((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1))‖ ≤
      8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε)) := by
  have ht : 0 < 1 + |t| := by positivity
  have hden := Analytic.denominator_ge (t := t) hσ
  have hsplit : (1 + |t|) ^ (-(2 - 2 * ε)) = (1 + |t|) ^ (2 * ε) / (1 + |t|) ^ 2 := by
    rw [show -(2 - 2 * ε) = 2 * ε - 2 by ring, Real.rpow_sub ht, Real.rpow_two]
  have hL := hB.trans (mul_le_mul_of_nonneg_left (scale_le q t hε) hD)
  rw [norm_div, hsplit]
  calc ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ /
        ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)‖
      ≤ D * ((18 * q) ^ ε * (1 + |t|) ^ (2 * ε)) / ((1 + |t|) ^ 2 / 8) := by
        gcongr
    _ = 8 * D * (18 * q) ^ ε * ((1 + |t|) ^ (2 * ε) / (1 + |t|) ^ 2) := by
        field_simp

theorem integrand_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x D ε : ℝ}
    (hx : 0 < x) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hB : ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      8 * D * (18 * q) ^ ε * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) := by
  have hpow : ‖((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  unfold integrand
  rw [norm_mul, hpow]
  have h := quotient_norm_le χ hσ hD hε hB
  have hxσ : 0 ≤ x ^ σ := by positivity
  calc x ^ σ * ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I) /
        (((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1))‖
      ≤ x ^ σ * (8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε))) := by gcongr
    _ = _ := by ring

/-- The Riesz mean of `χ` as an integral over the line `re s = σ₀`. -/
theorem rieszSum_eq_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x D ε σ₀ : ℝ} (hx : 1 ≤ x) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    Riesz.rieszSum ↗χ x =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, integrand χ x ((σ₀ : ℂ) + (t : ℂ) * I) := by
  have hx0 : 0 < x := by linarith
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 - 2 * ε))) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2 - 2 * ε)
      (by rw [Module.finrank_self]; push_cast; linarith)
    simpa only [Real.norm_eq_abs] using h
  set c : ℝ := 8 * D * (18 * q) ^ ε with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 → ∀ t : ℝ,
      ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ c * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) :=
    fun σ h1 h2 t => integrand_norm_le χ hx0 (by linarith) hD hε (hB σ t h1 h2)
  have hdiff : ∀ z : ℂ, σ₀ ≤ z.re → z.re ≤ 2 → DifferentiableAt ℂ (integrand χ x) z :=
    fun z h1 _ => integrand_differentiableAt χ hχ hx0 (by linarith)
  have hcont : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      Continuous (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.comp (g := integrand χ x)
    · exact (hdiff _ (by simpa using h1) (by simpa using h2)).continuousAt
    · fun_prop
  have hint : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    refine Integrable.mono' (hI.const_mul (c * x ^ σ))
      (hcont σ h1 h2).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun t => by simpa [mul_assoc] using hpt σ h1 h2 t)
  have hgrowth : ∀ σ ∈ Icc σ₀ 2, ∀ t : ℝ,
      ‖integrand χ x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (c * x ^ (2 : ℝ)) * Real.exp (0 * |t|) := by
    intro σ hσ t
    rw [zero_mul, Real.exp_zero, mul_one]
    refine (hpt σ hσ.1 hσ.2 t).trans ?_
    have h1 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have h2 : (1 + |t|) ^ (-(2 - 2 * ε)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
    have h4 : 0 ≤ (1 + |t|) ^ (-(2 - 2 * ε)) := by positivity
    calc c * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) ≤ c * x ^ (2 : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 h4 (by positivity)
      _ = _ := by ring
  have hshift := ContourShift.integral_eq_of_exponential_strip_growth (integrand χ x) σ₀ 2 0
    (c * x ^ (2 : ℝ)) hσ₀' le_rfl (by positivity) hdiff
    (hint σ₀ le_rfl hσ₀') (hint 2 hσ₀' le_rfl) hgrowth
  have hsum : LSeriesSummable ↗χ ((2 : ℝ) : ℂ) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ (by simp)
  have hR := Riesz.rieszSum_mellinInv (σ := 2) (by norm_num) hx0 ↗χ hsum
  have hline : mellinInv 2 (fun s => LSeries ↗χ s / (s * (s + 1))) (1 / x) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, integrand χ x (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall (fun t => ?_)
    have hre : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by simp
    simp only [integrand, smul_eq_mul]
    rw [← DirichletCharacter.LFunction_eq_LSeries χ hre]
  rw [← hR, hline, ← hshift]


theorem integrable_decay {r : ℝ} (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-r)) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by rw [Module.finrank_self]; push_cast; linarith)
  simpa only [Real.norm_eq_abs] using h

theorem integrand_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x D ε σ : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2) (hσ : 1 / 2 ≤ σ)
    (hB : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    Integrable (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
  have hI := integrable_decay (r := 2 - 2 * ε) (by linarith)
  have hcont : Continuous (fun t : ℝ => integrand χ x ((σ : ℂ) + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.comp (g := integrand χ x)
    · exact (integrand_differentiableAt χ hχ hx (by simp; linarith)).continuousAt
    · fun_prop
  refine Integrable.mono' (hI.const_mul (8 * D * (18 * q) ^ ε * x ^ σ))
    hcont.aestronglyMeasurable ?_
  exact Eventually.of_forall (fun t => integrand_norm_le χ hx hσ hD hε (hB t))

/-- `y · x^{-z}`-form of the integrand: `y · integrand = y^{z+1} L(z) / (z (z + 1))`. -/
theorem ofReal_mul_integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {y : ℝ}
    (hy : 0 < y) (z : ℂ) :
    (y : ℂ) * integrand χ y z =
      (y : ℂ) ^ (z + 1) * (DirichletCharacter.LFunction χ z / (z * (z + 1))) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hy1 : ((1 / y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.mpr hy).ne'
  have h1 : ((1 / y : ℝ) : ℂ) ^ (-z) = (y : ℂ) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hy1, Complex.cpow_def_of_ne_zero hy0,
      ← Complex.ofReal_log (one_div_pos.mpr hy).le, ← Complex.ofReal_log hy.le, one_div,
      Real.log_inv]
    push_cast
    congr 1
    ring
  unfold integrand
  rw [h1, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  ring

/-- The difference of two Riesz means as an integral over the line `re s = σ₀`. -/
theorem diff_eq_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x h D ε σ₀ : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ((x + h : ℝ) : ℂ) * Riesz.rieszSum ↗χ (x + h) - (x : ℂ) * Riesz.rieszSum ↗χ x =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
          (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)) *
        (DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I) /
          (((σ₀ : ℂ) + (t : ℂ) * I) * ((σ₀ : ℂ) + (t : ℂ) * I + 1))) := by
  have hx0 : 0 < x := by linarith
  have hxh : 0 < x + h := by linarith
  have hI1 := integrand_integrable χ hχ hxh hD hε hε' hσ₀ (fun t => hB σ₀ t le_rfl hσ₀')
  have hI2 := integrand_integrable χ hχ hx0 hD hε hε' hσ₀ (fun t => hB σ₀ t le_rfl hσ₀')
  rw [rieszSum_eq_line χ hχ (show 1 ≤ x + h by linarith) hD hε hε' hσ₀ hσ₀' hB,
    rieszSum_eq_line χ hχ hx hD hε hε' hσ₀ hσ₀' hB, mul_smul_comm, mul_smul_comm, ← smul_sub,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (hI1.const_mul _)
      (hI2.const_mul _)]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall (fun t => ?_)
  dsimp only
  rw [ofReal_mul_integrand χ hxh, ofReal_mul_integrand χ hx0]
  ring

/-- `‖(x + h)^w - x^w‖ ≤ ‖w‖ (x + h)^σ h` for `re w = σ + 1`, `σ ≥ 0`. -/
theorem cpow_sub_norm_le {x h σ : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hσ : 0 ≤ σ) {w : ℂ}
    (hw : w.re = σ + 1) :
    ‖((x + h : ℝ) : ℂ) ^ w - (x : ℂ) ^ w‖ ≤ ‖w‖ * (x + h) ^ σ * h := by
  have hderiv : ∀ u ∈ Icc x (x + h), HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ w)
      (w * (u : ℂ) ^ (w - 1)) (Icc x (x + h)) u := by
    intro u hu
    have hu0 : 0 < u := hx.trans_le hu.1
    exact ((Complex.hasStrictDerivAt_cpow_const
      (Complex.ofReal_mem_slitPlane.mpr hu0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ u ∈ Ico x (x + h), ‖w * (u : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * (x + h) ^ σ := by
    intro u hu
    have hu0 : 0 < u := hx.trans_le hu.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (w - 1).re = σ := by simp [hw]
    rw [hre]
    gcongr
    exact hu.2.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (x + h)
    ⟨by linarith, le_rfl⟩
  simpa using this

/-- `‖(x + h)^w - x^w‖ ≤ 2 (x + h)^{σ + 1}` for `re w = σ + 1`, `σ ≥ 0`. -/
theorem cpow_sub_norm_le' {x h σ : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hσ : 0 ≤ σ) {w : ℂ}
    (hw : w.re = σ + 1) :
    ‖((x + h : ℝ) : ℂ) ^ w - (x : ℂ) ^ w‖ ≤ 2 * (x + h) ^ (σ + 1) := by
  have hxh : 0 < x + h := by linarith
  have hm : x ^ (σ + 1) ≤ (x + h) ^ (σ + 1) :=
    Real.rpow_le_rpow hx.le (by linarith) (by linarith)
  calc _ ≤ ‖((x + h : ℝ) : ℂ) ^ w‖ + ‖(x : ℂ) ^ w‖ := norm_sub_le _ _
    _ = (x + h) ^ (σ + 1) + x ^ (σ + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh, Complex.norm_cpow_eq_rpow_re_of_pos hx, hw]
    _ ≤ 2 * (x + h) ^ (σ + 1) := by linarith

/-- If `N ≤ M a` and `N ≤ M b`, then `N ≤ M a^{1-θ} b^θ`. -/
theorem le_interp {N M a b θ : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : N ≤ M * a) (h2 : N ≤ M * b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    N ≤ M * (a ^ (1 - θ) * b ^ θ) := by
  have hs : (1 - θ) + θ = 1 := by ring
  have hpow : ∀ y : ℝ, 0 ≤ y → y ^ (1 - θ) * y ^ θ = y := fun y hy => by
    rw [← Real.rpow_add' hy (by rw [hs]; norm_num), hs, Real.rpow_one]
  calc N = N ^ (1 - θ) * N ^ θ := (hpow N hN).symm
    _ ≤ (M * a) ^ (1 - θ) * (M * b) ^ θ :=
        mul_le_mul (Real.rpow_le_rpow hN h1 (by linarith)) (Real.rpow_le_rpow hN h2 hθ0)
          (by positivity) (Real.rpow_nonneg (hN.trans h1) _)
    _ = (M ^ (1 - θ) * M ^ θ) * (a ^ (1 - θ) * b ^ θ) := by
        rw [Real.mul_rpow hM ha, Real.mul_rpow hM hb]; ring
    _ = M * (a ^ (1 - θ) * b ^ θ) := by rw [hpow M hM]

/-- The bound for the difference of two Riesz means. -/
theorem diff_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {x h D ε σ₀ : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hD : 0 ≤ D) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum ↗χ (x + h) - (x : ℂ) * Riesz.rieszSum ↗χ x‖ ≤
      1 / (2 * Real.pi) * (8 * D * (18 * q) ^ ε) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) *
        ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) := by
  have hx0 : 0 < x := by linarith
  have hxh : 0 < x + h := by linarith
  have hM : 0 ≤ (x + h) ^ σ₀ := Real.rpow_nonneg hxh.le _
  have hc : 0 ≤ 8 * D * (18 * q) ^ ε := by positivity
  have hW : 0 ≤ (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)) := by
    positivity
  rw [diff_eq_line χ hχ hx hh hD hε.le (by linarith) hσ₀ hσ₀' hB, norm_smul]
  have hpt : ∀ t : ℝ, ‖(((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)) *
        (DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (t : ℂ) * I) /
          (((σ₀ : ℂ) + (t : ℂ) * I) * ((σ₀ : ℂ) + (t : ℂ) * I + 1)))‖ ≤
        (8 * D * (18 * q) ^ ε) *
          ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
          (1 + |t|) ^ (-(1 + 2 * ε)) := by
    intro t
    have ht : 0 < 1 + |t| := by positivity
    have hw : ((σ₀ : ℂ) + (t : ℂ) * I + 1).re = σ₀ + 1 := by simp
    have hN1 := cpow_sub_norm_le hx0 hh (by linarith) hw
    have hN2 := cpow_sub_norm_le' hx0 hh (by linarith) hw
    have hz1 : ‖(σ₀ : ℂ) + (t : ℂ) * I + 1‖ ≤ 3 * (1 + |t|) := by
      have he : (σ₀ : ℂ) + (t : ℂ) * I + 1 = ((σ₀ + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [he]
      calc ‖((σ₀ + 1 : ℝ) : ℂ) + (t : ℂ) * I‖
          ≤ ‖((σ₀ + 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |σ₀ + 1| + |t| := by
            simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 3 * (1 + |t|) := by
            rw [abs_of_pos (by linarith)]; linarith [abs_nonneg t]
    have hA : ‖((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)‖ ≤ (x + h) ^ σ₀ * (3 * h * (1 + |t|)) := by
      calc _ ≤ ‖(σ₀ : ℂ) + (t : ℂ) * I + 1‖ * (x + h) ^ σ₀ * h := hN1
        _ ≤ 3 * (1 + |t|) * (x + h) ^ σ₀ * h := by gcongr
        _ = (x + h) ^ σ₀ * (3 * h * (1 + |t|)) := by ring
    have hBd : ‖((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)‖ ≤ (x + h) ^ σ₀ * (2 * (x + h)) := by
      calc _ ≤ 2 * (x + h) ^ (σ₀ + 1) := hN2
        _ = (x + h) ^ σ₀ * (2 * (x + h)) := by
            rw [Real.rpow_add_one hxh.ne']; ring
    have hint := le_interp (norm_nonneg _) hM (by positivity) (by positivity) hA hBd
      (show 0 ≤ 4 * ε by linarith) (show 4 * ε ≤ 1 by linarith)
    have hQ := quotient_norm_le χ (σ := σ₀) (t := t) hσ₀ hD hε.le (hB σ₀ t le_rfl hσ₀')
    have hsplit : (3 * h * (1 + |t|)) ^ (1 - 4 * ε) =
        (3 * h) ^ (1 - 4 * ε) * (1 + |t|) ^ (1 - 4 * ε) :=
      Real.mul_rpow (by positivity) ht.le
    have hexp : (1 + |t|) ^ (1 - 4 * ε) * (1 + |t|) ^ (-(2 - 2 * ε)) =
        (1 + |t|) ^ (-(1 + 2 * ε)) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [norm_mul]
    calc _ ≤ ((x + h) ^ σ₀ * ((3 * h * (1 + |t|)) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
          (8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε))) :=
          mul_le_mul hint hQ (norm_nonneg _) (by positivity)
      _ = (8 * D * (18 * q) ^ ε) *
            ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
            ((1 + |t|) ^ (1 - 4 * ε) * (1 + |t|) ^ (-(2 - 2 * ε))) := by
          rw [hsplit]; ring
      _ = _ := by rw [hexp]
  have hI := integrable_decay (r := 1 + 2 * ε) (by linarith)
  have hpi : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hbound := norm_integral_le_of_norm_le
    (hI.const_mul ((8 * D * (18 * q) ^ ε) *
      ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)))))
    (Eventually.of_forall hpt)
  rw [integral_const_mul] at hbound
  calc _ ≤ 1 / (2 * Real.pi) * ((8 * D * (18 * q) ^ ε) *
        ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
        ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) := by gcongr
    _ = _ := by ring

/-- `h ‖∑_{n ≤ x} a(n)‖ ≤ ‖(x + h) R(x + h) - x R(x)‖ + h (h + 1)` for `‖a(n)‖ ≤ 1`. -/
theorem unsmooth (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤
      ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x‖ +
        h * (h + 1) := by
  have hT : ∀ y : ℝ, 0 < y → (y : ℂ) * Riesz.rieszSum a y =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, a n * ((y : ℂ) - n) := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    unfold Riesz.rieszSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    field_simp
  have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit := Finset.sum_Ioc_consecutive (fun n => a n * (((x + h : ℝ) : ℂ) - n))
    (Nat.zero_le ⌊x⌋₊) hle
  have hmain : ((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x =
      (h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
    rw [hT (x + h) (by linarith), hT x hx, ← hsplit, Finset.mul_sum]
    have hs : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (((x + h : ℝ) : ℂ) - n) =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((h : ℂ) * a n + a n * ((x : ℂ) - n)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      push_cast
      ring
    rw [hs, Finset.sum_add_distrib]
    ring
  have htail : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)‖ ≤
      h * (h + 1) := by
    calc _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n * (((x + h : ℝ) : ℂ) - n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, h := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
          have hn1 : x < n := Nat.lt_of_floor_lt h1
          have hn2 : (n : ℝ) ≤ x + h := (Nat.le_floor_iff (by linarith)).mp h2
          have he : ((x + h : ℝ) : ℂ) - n = ((x + h - n : ℝ) : ℂ) := by push_cast; ring
          rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          calc ‖a n‖ * (x + h - n) ≤ 1 * h :=
                mul_le_mul (ha n) (by linarith) (by linarith) zero_le_one
            _ = h := one_mul h
      _ = ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) * h := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (h + 1) * h := by
          gcongr
          rw [Nat.cast_sub hle]
          have h1 := Nat.floor_le (show 0 ≤ x + h by linarith)
          have h2 := Nat.lt_floor_add_one x
          linarith
      _ = h * (h + 1) := by ring
  have hS : (h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n =
      (((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x) -
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
    rw [hmain]; ring
  calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ = ‖(h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    _ ≤ _ := by
        rw [hS]
        exact (norm_sub_le _ _).trans (by gcongr)

/-- **Character sums.** If `L(s, χ)` has no zero with `re s > a + 2e`, then
`‖∑_{n ≤ x} χ(n)‖ ≤ K q^ε x^{a + 8e + 4ε}` for `x ≥ 1`, with `K` depending only on `e`, `ε`. -/
theorem charSum_bound {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (hε' : ε ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ a : ℝ, 1 / 2 ≤ a → a + 8 * e ≤ 1 →
      (∀ z : ℂ, a + 2 * e < z.re → DirichletCharacter.LFunction χ z ≠ 0) →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖ ≤ K * (q : ℝ) ^ ε * x ^ (a + 8 * e + 4 * ε) := by
  obtain ⟨D, hD, hDb⟩ := norm_bound he he' hε
  have hJ0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) :=
    integral_nonneg (fun t => by positivity)
  refine ⟨1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24 + 2,
    by positivity, ?_⟩
  intro q _ χ hχ a ha ha1 hzero x hx
  have hx0 : 0 < x := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have he8 : 0 < 8 * e := by linarith
  have hB : ∀ σ t : ℝ, a + 8 * e ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε :=
    fun σ t h1 h2 => le_trans (le_add_of_nonneg_right (norm_nonneg _))
      (hDb q χ hχ a ha (by linarith) hzero σ t h1 h2)
  set σ₀ := a + 8 * e with hσ₀
  set h : ℝ := x ^ σ₀ with hhdef
  have hh1 : 1 ≤ h := Real.one_le_rpow hx (by linarith)
  have hh0 : 0 < h := by linarith
  have hhx : h ≤ x := by
    calc h = x ^ σ₀ := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx ha1
      _ = x := Real.rpow_one x
  have hdiff := diff_norm_le χ hχ hx hh0.le hD.le hε hε' (by linarith) (by linarith) hB
  have hun := unsmooth ↗χ (fun n => DirichletCharacter.norm_le_one χ n) hx0 hh0
  set X : ℝ := x ^ (σ₀ + 4 * ε) with hX
  set Q : ℝ := (q : ℝ) ^ ε with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hq hε.le
  have hx4 : 1 ≤ x ^ (4 * ε) := Real.one_le_rpow hx (by linarith)
  have hXsplit : X = h * x ^ (4 * ε) := Real.rpow_add hx0 _ _
  have hhX : h ≤ X := by rw [hXsplit]; nlinarith
  have hX1 : 1 ≤ X := hh1.trans hhX
  have h18 : (18 * (q : ℝ)) ^ ε ≤ 18 * Q := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
    calc (18 : ℝ) ^ ε ≤ 18 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 18 := Real.rpow_one 18
  have hW : (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)) ≤
      24 * h * X := by
    have h1 : (x + h) ^ σ₀ ≤ 2 * h := by
      calc (x + h) ^ σ₀ ≤ (2 * x) ^ σ₀ := Real.rpow_le_rpow (by linarith) (by linarith)
            (by linarith)
        _ = 2 ^ σ₀ * h := Real.mul_rpow (by norm_num) hx0.le
        _ ≤ 2 ^ (1 : ℝ) * h := by
            gcongr
            norm_num
        _ = 2 * h := by rw [Real.rpow_one]
    have h2 : (3 * h) ^ (1 - 4 * ε) ≤ 3 * h := by
      calc (3 * h) ^ (1 - 4 * ε) ≤ (3 * h) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 3 * h := Real.rpow_one _
    have h3 : (2 * (x + h)) ^ (4 * ε) ≤ 4 * x ^ (4 * ε) := by
      calc (2 * (x + h)) ^ (4 * ε) ≤ (4 * x) ^ (4 * ε) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ = 4 ^ (4 * ε) * x ^ (4 * ε) := Real.mul_rpow (by norm_num) hx0.le
        _ ≤ 4 ^ (1 : ℝ) * x ^ (4 * ε) := by
            gcongr
            · norm_num
            · linarith
        _ = 4 * x ^ (4 * ε) := by rw [Real.rpow_one]
    have hp2 : 0 ≤ (3 * h) ^ (1 - 4 * ε) := Real.rpow_nonneg (by linarith) _
    have hp3 : 0 ≤ (2 * (x + h)) ^ (4 * ε) := Real.rpow_nonneg (by linarith) _
    calc (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))
        ≤ (2 * h) * ((3 * h) * (4 * x ^ (4 * ε))) := by gcongr
      _ = 24 * h * (h * x ^ (4 * ε)) := by ring
      _ ≤ 24 * h * X := by rw [hXsplit]
  set J := ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) with hJ
  have hstep : 1 / (2 * Real.pi) * (8 * D * (18 * q) ^ ε) * J *
      ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) ≤
      1 / (2 * Real.pi) * (8 * D * (18 * Q)) * J * (24 * h * X) := by
    gcongr
  have hun' : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖ ≤
      ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum ↗χ (x + h) - (x : ℂ) * Riesz.rieszSum ↗χ x‖ +
        h * (h + 1) := hun
  set c := 1 / (2 * Real.pi) * (8 * D * 18) * J * 24 with hc
  have hmain : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖ ≤ h * (c * Q * X + h + 1) := by
    calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖
        ≤ 1 / (2 * Real.pi) * (8 * D * (18 * Q)) * J * (24 * h * X) + h * (h + 1) := by
          linarith [hun', hdiff, hstep]
      _ = h * (c * Q * X + h + 1) := by rw [hc]; ring
  have hS := le_of_mul_le_mul_left hmain hh0
  have hQX : X ≤ Q * X := by nlinarith
  show ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖ ≤ (c + 2) * Q * X
  nlinarith

/-- **Lindelöf bound to the right of `7/8`.** For every `w > 0` there is `C` such that
`‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |t|))^w` for every nonprincipal `χ` modulo `q` and every
`s` with `re s ≥ 7/8 + w`, `t = im s`. -/
theorem lindelof {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 7 / 8 + w ≤ s.re →
        ‖DirichletCharacter.LFunction χ s‖ + ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
          C * ((q : ℝ) * (3 + |s.im|)) ^ w := by
  set e := min (w / 8) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he8 : 8 * e ≤ w := by have := min_le_left (w / 8) (1 / 2000); linarith
  have he6 : 6 * e ≤ 1 / 8 := by have := min_le_right (w / 8) (1 / 2000); linarith
  obtain ⟨D, hD, hDb⟩ := norm_bound he he' (show 0 < w / 2 by linarith)
  set B := Real.exp EulerLog.eulerLogBound with hB
  have hB0 : 0 < B := Real.exp_pos _
  refine ⟨D * 2 ^ w + 2 * B, by positivity, ?_⟩
  intro q _ χ hχ s hs
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Y := (q : ℝ) * (3 + |s.im|) with hY
  have hY1 : 1 ≤ Y := by nlinarith [abs_nonneg s.im]
  have hYw : 1 ≤ Y ^ w := Real.one_le_rpow hY1 hw.le
  have hs_eq : (s.re : ℂ) + (s.im : ℂ) * I = s := Complex.re_add_im s
  by_cases h2 : s.re ≤ 2
  · have hb := hDb q χ hχ (7 / 8 - 2 * e) (by linarith) (by linarith)
      (fun z hz => zeroFree q χ hχ z (by linarith)) s.re s.im (by linarith) h2
    rw [hs_eq] at hb
    have hle : 2 * (q : ℝ) * (3 + |s.im|) ^ 2 ≤ (2 * Y) ^ 2 := by
      rw [hY]; nlinarith [abs_nonneg s.im]
    have hpow : (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) ≤ 2 ^ w * Y ^ w := by
      calc (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) ≤ ((2 * Y) ^ 2) ^ (w / 2) :=
            Real.rpow_le_rpow (by positivity) hle (by linarith)
        _ = (2 * Y) ^ w := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            congr 1
            push_cast
            ring
        _ = 2 ^ w * Y ^ w := Real.mul_rpow (by norm_num) (by positivity)
    calc _ ≤ D * (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) := hb
      _ ≤ D * (2 ^ w * Y ^ w) := by gcongr
      _ ≤ (D * 2 ^ w + 2 * B) * Y ^ w := by nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) w]
  · replace h2 := not_le.mp h2
    have hE := EulerLog.eulerLog_norm_le χ (s := s) (by linarith)
    have hexp := EulerLog.exp_eulerLog χ (s := s) (by linarith)
    set E := EulerLog.eulerLog χ s
    have h1 : ‖DirichletCharacter.LFunction χ s‖ ≤ B := by
      rw [← hexp, Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm E).trans hE)
    have h2' : ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ B := by
      rw [← hexp, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      refine Real.exp_le_exp.mpr ?_
      have := Complex.abs_re_le_norm E
      linarith [neg_le_abs E.re]
    have hD2 : 0 ≤ D * 2 ^ w := by positivity
    nlinarith

/-- **Character sums.** For every `w > 0` there is `C` such that
`‖∑_{1 ≤ n ≤ x} χ(n)‖ ≤ C q^w x^{7/8 + w}` for every nonprincipal `χ` modulo `q` and `x ≥ 1`. -/
theorem character_sum_bound {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * (q : ℝ) ^ w * x ^ (7 / 8 + w) := by
  set d := min w 1 with hd_def
  have hd : 0 < d := lt_min hw one_pos
  have hdw : d ≤ w := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  set e := min (d / 12) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he12 : 12 * e ≤ d := by have := min_le_left (d / 12) (1 / 2000); linarith
  have he6 : 6 * e ≤ 1 / 8 := by have := min_le_right (d / 12) (1 / 2000); linarith
  obtain ⟨K, hK, hKb⟩ := charSum_bound he he' (show 0 < d / 8 by linarith)
    (show d / 8 ≤ 1 / 8 by linarith)
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ x hx
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hI : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI]
  have hb := hKb q χ hχ (7 / 8 - 2 * e) (by linarith) (by linarith)
    (fun z hz => zeroFree q χ hχ z (by linarith)) x hx
  have hqp : (q : ℝ) ^ (d / 8) ≤ (q : ℝ) ^ w :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hxp : x ^ (7 / 8 - 2 * e + 8 * e + 4 * (d / 8)) ≤ x ^ (7 / 8 + w) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc _ ≤ K * (q : ℝ) ^ (d / 8) * x ^ (7 / 8 - 2 * e + 8 * e + 4 * (d / 8)) := hb
    _ ≤ K * (q : ℝ) ^ w * x ^ (7 / 8 + w) := by gcongr

/-- **Vinogradov's character sum conjecture.** For every `η > 0` and `θ > 7/8` there is `C`
such that `‖∑_{1 ≤ n ≤ x} χ(n)‖ ≤ C x^θ` for every nonprincipal `χ` modulo `q` and every
`x ≥ q^η`. -/
theorem character_sum_le_rpow {η θ : ℝ} (hη : 0 < η) (hθ : 7 / 8 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ^ η ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * x ^ θ := by
  set w := (θ - 7 / 8) * η / (1 + η) with hw_def
  have hw : 0 < w := by positivity
  obtain ⟨C, hC, hCb⟩ := character_sum_bound hw
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ x hx hqx
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqd : (q : ℝ) ^ w ≤ x ^ (w / η) := by
    calc (q : ℝ) ^ w = ((q : ℝ) ^ η) ^ (w / η) := by
          rw [← Real.rpow_mul hq0]; congr 1; field_simp
      _ ≤ x ^ (w / η) := Real.rpow_le_rpow (by positivity) hqx (by positivity)
  have hexp : w / η + (7 / 8 + w) = θ := by
    rw [hw_def]; field_simp; ring
  calc _ ≤ C * (q : ℝ) ^ w * x ^ (7 / 8 + w) := hCb q χ hχ x hx
    _ ≤ C * x ^ (w / η) * x ^ (7 / 8 + w) := by gcongr
    _ = C * x ^ θ := by rw [mul_assoc, ← Real.rpow_add hx0, hexp]

end Vinogradov.CharSum
