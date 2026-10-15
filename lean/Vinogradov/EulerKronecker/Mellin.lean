import Mathlib
import Vinogradov.Riesz

/-!
# The Mellin transform of a Riesz sum

For `re s > 0` and an `L`-series absolutely convergent at `s`,
`∫_0^∞ x^{-s-1} ∑_{n ≤ x} a n (1 - n/x) dx = L(a, s) / (s (s + 1))`.
-/

namespace Vinogradov.EulerKronecker

open Complex Real Set MeasureTheory Filter Topology Asymptotics
open Vinogradov.Riesz
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

lemma rieszKernel_norm_le (t : ℝ) :
    ‖rieszKernel t‖ ≤ (Ioc 0 1).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [rieszKernel, indicator_of_mem ht, indicator_of_mem ht]
    have h1 : (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_of_nonneg (by linarith [ht.2])]
    linarith [ht.1]
  · simp [rieszKernel, ht]

lemma hasMellin_rieszKernel_dilate {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasMellin (fun y => rieszKernel (n * y)) s ((n : ℂ) ^ (-s) * (1 / (s * (s + 1)))) := by
  have h := hasMellin_rieszKernel hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨(MellinConvergent.comp_mul_left hn').mpr h.1, ?_⟩
  rw [mellin_comp_mul_left _ _ hn', h.2, smul_eq_mul, Complex.ofReal_natCast]

/-- The `n`-th term of the Riesz sum, as a function of `y = 1/x`. -/
noncomputable def rterm (a : ℕ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  if n = 0 then 0 else a n * rieszKernel ((n : ℝ) * y)

lemma integrableOn_rterm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • rterm a n y) (Ioi 0) := by
  by_cases hn : n = 0
  · simp [rterm, hn]
  · have h := ((hasMellin_rieszKernel_dilate hs hn).1).const_smul (a n)
    unfold MellinConvergent at h
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [rterm, hn, ↓reduceIte, smul_eq_mul]

lemma mellin_rterm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (s - 1) • rterm a n y = LSeries.term a s n / (s * (s + 1)) := by
  by_cases hn : n = 0
  · simp [rterm, hn]
  · have h := (hasMellin_rieszKernel_dilate hs hn).2
    unfold mellin at h
    have he : ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (s - 1) • rterm a n y =
        a n * ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (s - 1) • rieszKernel (n * y) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      simp only [rterm, hn, ↓reduceIte, smul_eq_mul]
      ring
    rw [he, h, LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    field_simp

lemma integral_norm_rterm_le (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ y in Ioi (0:ℝ), ‖(y : ℂ) ^ (s - 1) • rterm a n y‖ ≤ ‖LSeries.term a s n‖ / s.re := by
  by_cases hn : n = 0
  · simp [rterm, hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set b : ℝ := 1 / n with hb
  have hb0 : 0 < b := by positivity
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • rterm a n y‖ ≤
      ‖a n‖ * (Ioc 0 b).indicator (fun y => y ^ (s.re - 1)) y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [rterm, hn, ↓reduceIte, smul_eq_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.sub_re, Complex.one_re]
    have hk := rieszKernel_norm_le ((n : ℝ) * y)
    by_cases hyb : y ∈ Ioc 0 b
    · rw [indicator_of_mem hyb]
      have hk1 : ‖rieszKernel ((n : ℝ) * y)‖ ≤ 1 := by
        refine hk.trans ?_
        by_cases hm : (n : ℝ) * y ∈ Ioc (0 : ℝ) 1
        · rw [indicator_of_mem hm]
        · rw [indicator_of_notMem hm]; norm_num
      have hp : 0 ≤ y ^ (s.re - 1) := Real.rpow_nonneg hy0.le _
      calc y ^ (s.re - 1) * (‖a n‖ * ‖rieszKernel (↑n * y)‖)
          ≤ y ^ (s.re - 1) * (‖a n‖ * 1) := by gcongr
        _ = ‖a n‖ * y ^ (s.re - 1) := by ring
    · rw [indicator_of_notMem hyb]
      have hm : (n : ℝ) * y ∉ Ioc (0 : ℝ) 1 := by
        intro hm
        apply hyb
        refine ⟨hy0, ?_⟩
        rw [hb, le_div_iff₀ hn']
        linarith [hm.2]
      rw [indicator_of_notMem hm] at hk
      have : ‖rieszKernel ((n : ℝ) * y)‖ = 0 := le_antisymm hk (norm_nonneg _)
      rw [this]; simp
  have hint : IntegrableOn (fun y => ‖a n‖ * (Ioc 0 b).indicator (fun y => y ^ (s.re - 1)) y)
      (Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (s.re - 1)) (Ioc 0 b) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
        (r := s.re - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).mp this
    have h2 : Integrable ((Ioc 0 b).indicator (fun y : ℝ => y ^ (s.re - 1))) :=
      (integrable_indicator_iff measurableSet_Ioc).mpr h1
    exact (h2.const_mul ‖a n‖).integrableOn
  calc ∫ y in Ioi (0:ℝ), ‖(y : ℂ) ^ (s - 1) • rterm a n y‖
      ≤ ∫ y in Ioi (0:ℝ), ‖a n‖ * (Ioc 0 b).indicator (fun y => y ^ (s.re - 1)) y :=
        setIntegral_mono_on (integrableOn_rterm a hs n).norm hint measurableSet_Ioi hpt
    _ = ‖a n‖ * ∫ y in Ioc 0 b, y ^ (s.re - 1) := by
        rw [integral_const_mul, setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr (Ioc_subset_Ioi_self)]
    _ = ‖a n‖ * (b ^ s.re / s.re) := by
        rw [← intervalIntegral.integral_of_le hb0.le, integral_rpow (Or.inl (by linarith))]
        rw [sub_add_cancel, Real.zero_rpow hs.ne']
        ring
    _ = ‖LSeries.term a s n‖ / s.re := by
        rw [LSeries.norm_term_eq]
        simp only [hn, ↓reduceIte]
        rw [hb, Real.div_rpow zero_le_one hn'.le, Real.one_rpow]
        ring

theorem mellin_tsum_rterm (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (ha : LSeriesSummable a s) :
    mellin (fun y => ∑' n, rterm a n y) s = LSeries a s / (s * (s + 1)) := by
  have hint : ∀ n, Integrable (fun y : ℝ => (y : ℂ) ^ (s - 1) • rterm a n y)
      (volume.restrict (Ioi (0 : ℝ))) := fun n => integrableOn_rterm a hs n
  have hsum : Summable (fun n => ∫ y in Ioi (0:ℝ), ‖(y : ℂ) ^ (s - 1) • rterm a n y‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => integral_norm_rterm_le a hs n) (ha.norm.div_const _)
  have hS := (hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq
  unfold mellin
  have hpt : (fun y : ℝ => (y : ℂ) ^ (s - 1) • ∑' n, rterm a n y) =
      (fun y : ℝ => ∑' n, (y : ℂ) ^ (s - 1) • rterm a n y) := by
    ext y
    simp only [smul_eq_mul]
    rw [tsum_mul_left]
  rw [hpt, ← hS]
  simp_rw [mellin_rterm a hs]
  rw [tsum_div_const]
  rfl

lemma rieszSum_inv_eq (a : ℕ → ℂ) {y : ℝ} (hy : 0 < y) :
    rieszSum a y⁻¹ = ∑' n, rterm a n y := by
  rw [← rieszKernel_tsum_eq (inv_pos.mpr hy) a]
  congr 1
  ext n
  simp [rterm]

/-- The Mellin transform of a Riesz sum at `-s`. -/
theorem mellin_rieszSum (a : ℕ → ℂ) {s : ℂ} (hs : 0 < s.re) (ha : LSeriesSummable a s) :
    mellin (rieszSum a) (-s) = LSeries a s / (s * (s + 1)) := by
  rw [← mellin_comp_inv]
  have h : mellin (fun t => rieszSum a t⁻¹) s = mellin (fun y => ∑' n, rterm a n y) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [rieszSum_inv_eq a hy]
  rw [h, mellin_tsum_rterm a hs ha]

lemma rieszSum_eq_zero_of_lt_one (a : ℕ → ℂ) {x : ℝ} (hx : x < 1) : rieszSum a x = 0 := by
  have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [rieszSum, this]

lemma rieszSum_eq_finsum (a : ℕ → ℂ) {N : ℕ} {x : ℝ} (hx : 0 < x) (hxN : x < N) :
    rieszSum a x = ∑ n ∈ Finset.range N, rterm a n x⁻¹ := by
  rw [← inv_inv x, rieszSum_inv_eq a (inv_pos.mpr hx), inv_inv]
  refine tsum_eq_sum (fun n hn => ?_)
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast not_lt.mp (fun h => hn (Finset.mem_range.mpr h))
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn'
    have hN : (N : ℝ) ≤ 0 := by simpa using hn'
    linarith
  simp only [rterm, hn0, ↓reduceIte]
  have hm : ¬ ((n : ℝ) * x⁻¹ ∈ Ioc (0 : ℝ) 1) := by
    intro hm
    have : (n : ℝ) ≤ x := by
      have h2 := hm.2
      rwa [mul_inv_le_iff₀ hx, one_mul] at h2
    linarith
  rw [rieszKernel, indicator_of_notMem hm, mul_zero]

lemma rterm_continuousAt (a : ℕ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun x : ℝ => rterm a n x⁻¹) x := by
  by_cases hn : n = 0
  · simp only [rterm, hn, ↓reduceIte]; exact continuousAt_const
  · simp only [rterm, hn, ↓reduceIte]
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.comp (g := rieszKernel)
    · exact rieszKernel_continuousAt (mul_pos hn' (inv_pos.mpr hx))
    · exact continuousAt_const.mul (continuousAt_inv₀ hx.ne')

lemma rieszSum_continuousOn (a : ℕ → ℂ) : ContinuousOn (rieszSum a) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  apply ContinuousAt.continuousWithinAt
  set N : ℕ := ⌊x⌋₊ + 1
  have hxN : x < N := by simpa [N] using Nat.lt_floor_add_one x
  have he : (fun y => ∑ n ∈ Finset.range N, rterm a n y⁻¹) =ᶠ[𝓝 x] rieszSum a := by
    filter_upwards [Ioo_mem_nhds hx0 hxN] with y hy
    exact (rieszSum_eq_finsum a hy.1 hy.2).symm
  refine ContinuousAt.congr ?_ he
  exact tendsto_finsetSum _ (fun n _ => rterm_continuousAt a n hx0)

/-- If `‖∑_{n ≤ x} a n (1 - n/x)‖ ≤ K x^θ` for `x ≥ 1` with `θ < 1`, the Mellin transform of
the Riesz sum is differentiable at `-1`. -/
lemma mellin_rieszSum_differentiableAt (a : ℕ → ℂ) {θ K : ℝ} (hθ : θ < 1)
    (hR : ∀ x : ℝ, 1 ≤ x → ‖rieszSum a x‖ ≤ K * x ^ θ) :
    DifferentiableAt ℂ (mellin (rieszSum a)) (-1) := by
  apply mellin_differentiableAt_of_isBigO_rpow (a := -θ) (b := -2)
  · exact (rieszSum_continuousOn a).locallyIntegrableOn measurableSet_Ioi
  · simp only [neg_neg]
    refine IsBigO.of_bound K ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hR x hx
  · simp; linarith
  · simp only [neg_neg]
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [rieszSum_eq_zero_of_lt_one a hx.2]
    simp
  · simp

/-- Two functions continuous at `1` that agree on `re s > 1` agree at `1`. -/
lemma eq_at_one {f g : ℂ → ℂ} (hf : ContinuousAt f 1) (hg : ContinuousAt g 1)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f 1 = g 1 := by
  have hT : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).add h0
    rw [add_zero] at h1
    have := (Complex.continuous_ofReal.tendsto 1).comp h1
    rw [Complex.ofReal_one] at this
    exact this
  have h1 := hf.tendsto.comp hT
  have h2 := hg.tendsto.comp hT
  have heq : (f ∘ fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) =
      (g ∘ fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) := by
    funext n
    apply h
    simp only [Complex.ofReal_re]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The logarithmic derivative at `s = 1` as a Mellin integral.** If the Riesz sums of
`χ Λ` grow at most like `x^θ` with `θ < 1`, then
`-L'/L(1, χ) = 2 ∫_0^∞ x^{-2} ∑_{n ≤ x} χ(n) Λ(n) (1 - n/x) dx`. -/
theorem neg_logDeriv_one_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ K : ℝ} (hθ : θ < 1)
    (hR : ∀ x : ℝ, 1 ≤ x → ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ θ) :
    -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
      2 * mellin (rieszSum (↗χ * ↗Λ)) (-1) := by
  set a : ℕ → ℂ := ↗χ * ↗Λ with ha
  set Lf := DirichletCharacter.LFunction χ with hLf
  have hLd : Differentiable ℂ Lf := DirichletCharacter.differentiable_LFunction hχ
  have hL1 : Lf 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hderiv : Continuous (deriv Lf) := (hLd.contDiff (n := 1)).continuous_deriv le_rfl
  have hf : ContinuousAt (fun s => -deriv Lf s / Lf s) 1 :=
    (hderiv.continuousAt.neg).div (hLd 1).continuousAt hL1
  have hg : ContinuousAt (fun s : ℂ => s * (s + 1) * mellin (rieszSum a) (-s)) 1 := by
    have hm : ContinuousAt (fun s : ℂ => mellin (rieszSum a) (-s)) 1 := by
      have hd := mellin_rieszSum_differentiableAt a hθ hR
      exact (hd.continuousAt).comp (f := fun s : ℂ => -s) (by fun_prop)
    exact (by fun_prop : ContinuousAt (fun s : ℂ => s * (s + 1)) 1).mul hm
  have h := eq_at_one hf hg (fun s hs => ?_)
  · rw [h]; norm_num
  · have hs0 : 0 < s.re := by linarith
    have hsum : LSeriesSummable a s := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    have hM := mellin_rieszSum a hs0 hsum
    have hss : s * (s + 1) ≠ 0 := by
      apply mul_ne_zero
      · intro h0; rw [h0] at hs; simp at hs; linarith
      · intro h0; have := congrArg Complex.re h0; simp at this; linarith
    rw [hM, mul_div_cancel₀ _ hss, ha,
      DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : Lf =ᶠ[𝓝 s] LSeries ↗χ := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact DirichletCharacter.LFunction_eq_LSeries χ hz
    rw [hev.deriv_eq, hev.eq_of_nhds]

end Vinogradov.EulerKronecker
