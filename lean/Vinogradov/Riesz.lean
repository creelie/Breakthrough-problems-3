import Mathlib

/-!
# Riesz means as inverse Mellin transforms

For `σ ≥ 1`, `x > 0` and an `L`-series `∑ a n n^{-s}` absolutely convergent at `σ`,
`∑_{n ≤ x} a n (1 - n/x)` is the inverse Mellin transform of `L(s)/(s(s+1))` on the
line `re s = σ`, evaluated at `1/x`.

The proofs in this file are taken, with namespace changes only, from
`OAI/NumberTheory/PrimeGaps/MellinSmoothing.lean` of OpenAI's `math` repository
(Apache License 2.0).
-/

namespace Vinogradov.Riesz

open Complex Real Set MeasureTheory Filter Topology

noncomputable def rieszKernel : ℝ → ℂ := (Ioc 0 1).indicator (fun t => 1-(t:ℂ))

lemma hasMellin_rieszKernel {s : ℂ} (hs : 0<s.re) :
    HasMellin rieszKernel s (1/(s*(s+1))) := by
  have h₀ := hasMellin_one_Ioc hs
  have h₁ := hasMellin_cpow_Ioc 1 (by simp; linarith : 0<s.re+(1:ℂ).re)
  have hh := hasMellin_sub h₀.1 h₁.1
  rw [h₀.2,h₁.2] at hh
  have he : (fun t : ℝ => (Ioc 0 1).indicator (fun _ : ℝ => (1:ℂ)) t-
      (Ioc 0 1).indicator (fun t : ℝ => (t:ℂ)^(1:ℂ)) t)=rieszKernel := by
    ext t
    by_cases ht : t∈Ioc (0:ℝ) 1 <;> simp [rieszKernel,ht]
  rw [he] at hh
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have heval : 1/s-1/(s+1)=1/(s*(s+1)) := by field_simp; ring
  rwa [heval] at hh

lemma rieszKernel_eq_max {x : ℝ} (hx : 0<x) : rieszKernel x=(max (1-x) 0:ℝ) := by
  by_cases hx1 : x≤1
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1]
  · simp [rieszKernel,Set.mem_Ioc,hx,hx1,max_eq_right (by linarith : 1-x≤(0:ℝ))]

lemma rieszKernel_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt rieszKernel x := by
  have he : rieszKernel =ᶠ[𝓝 x] (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact rieszKernel_eq_max hy
  exact (show ContinuousAt (fun x : ℝ => ((max (1-x) 0:ℝ):ℂ)) x by fun_prop).congr he.symm

lemma rieszDenominator_bound {s : ℂ} (hs : 1≤ s.re) :
    ‖1/(s*(s+1))‖≤2/(1+s.im^2) := by
  have ha : 1≤‖s‖ := hs.trans (Complex.re_le_norm s)
  have hb : 1≤‖s+1‖ := by have h := Complex.re_le_norm (s+1); simp at h; linarith
  have hai : |s.im|≤‖s‖ := Complex.abs_im_le_norm s
  have hbi : |s.im|≤‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hp : 1≤‖s‖*‖s+1‖ := one_le_mul_of_one_le_of_one_le ha hb
  have hpi : s.im^2≤‖s‖*‖s+1‖ := by
    simpa only [←sq, sq_abs] using mul_le_mul hai hbi (abs_nonneg _) (norm_nonneg _)
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ (by positivity : 0<‖s‖*‖s+1‖) (by positivity : 0<1+s.im^2)).mpr
  nlinarith

lemma rieszDenominator_verticalIntegrable {σ : ℝ} (hσ : 1≤σ) :
    VerticalIntegrable (fun s : ℂ => 1/(s*(s+1))) σ := by
  have hne (t : ℝ) : (σ:ℂ)+(t:ℂ)*I≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne1 (t : ℝ) : (σ:ℂ)+(t:ℂ)*I+1≠0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hm : Continuous (fun t : ℝ => 1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    exact mul_ne_zero (hne t) (hne1 t)
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  have hb := rieszDenominator_bound (s:=(σ:ℂ)+t*I) (by simpa using hσ)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,mul_zero,
    Complex.ofReal_re,Complex.I_im,mul_one,add_zero,zero_add,div_eq_mul_inv] using hb

lemma rieszKernel_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x) :
    mellinInv σ (fun s : ℂ => 1/(s*(s+1))) x=rieszKernel x := by
  have hσ0 : (0:ℝ)<σ := by linarith
  have hm (t : ℝ) : mellin rieszKernel (σ+t*I)=1/((σ+t*I)*(σ+t*I+1)) :=
    (hasMellin_rieszKernel (by simpa using hσ0)).2
  have hF : VerticalIntegrable (mellin rieszKernel) σ := by
    unfold VerticalIntegrable
    simp_rw [hm]
    exact rieszDenominator_verticalIntegrable hσ
  rw [←mellinInv_mellin_eq σ rieszKernel hx (hasMellin_rieszKernel (by simpa using hσ0)).1 hF
    (rieszKernel_continuousAt hx)]
  simp only [mellinInv,hm]

open Complex Filter Topology

lemma mellinInv_const_mul (σ : ℝ) (f : ℂ → ℂ) (a : ℂ) (x : ℝ) :
    mellinInv σ (fun s => a*f s) x=a*mellinInv σ f x := by
  simp [mellinInv,smul_eq_mul,Complex.real_smul,mul_left_comm,integral_const_mul,mul_assoc]

lemma mellinInv_term_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (n : ℕ) :
    mellinInv σ (fun s => LSeries.term a s n/(s*(s+1))) y=
      if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  by_cases hn : n=0
  · simp [hn,mellinInv]
  rw [ite_eq_right hn]
  have hi := rieszKernel_mellinInv hσ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hy)
  rw [←hi]
  simp only [mellinInv,LSeries.term_of_ne_zero hn,smul_eq_mul,Complex.real_smul]
  rw [mul_left_comm (a n) ((1/(2*π):ℝ):ℂ)]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hy.le]
  simp only [Complex.ofReal_natCast,Complex.cpow_neg]
  ring

lemma riesz_inverse_integrand_norm {σ y : ℝ} (hy : 0<y) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    ‖(y:ℂ)^(-((σ:ℂ)+t*I))*(LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖=
      (y^(-σ)*‖LSeries.term a (σ:ℂ) n‖)*‖1/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))‖ := by
  simp only [norm_mul,norm_div,norm_one,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,LSeries.norm_term_eq]
  ring

lemma riesz_inverse_integrand_summable {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    (∀ n : ℕ, Integrable (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1))))) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
        (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
  have hc (n : ℕ) : Continuous (fun t : ℝ => (y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))) := by
    have hz (t : ℝ) : (σ:ℂ)+t*I≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hz1 (t : ℝ) : (σ:ℂ)+t*I+1≠0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hd : Continuous (fun t : ℝ => ((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)) := by fun_prop
    have he : Continuous (fun t : ℝ => -((σ:ℂ)+t*I)) := by fun_prop
    apply (he.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    apply Continuous.div _ hd (fun t => mul_ne_zero (hz t) (hz1 t))
    by_cases hn : n=0
    · simpa [hn] using (continuous_const : Continuous (fun _t : ℝ => (0:ℂ)))
    · simp only [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (σ:ℂ)+t*I) by fun_prop).const_cpow
          (.inl (Nat.cast_ne_zero.mpr hn))
      · intro t; exact Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn))
  have hnorm (n : ℕ) : Integrable (fun t : ℝ => ‖(y:ℂ)^(-((σ:ℂ)+t*I))*
      (LSeries.term a ((σ:ℂ)+t*I) n/(((σ:ℂ)+t*I)*((σ:ℂ)+t*I+1)))‖) := by
    simp_rw [riesz_inverse_integrand_norm hy]
    exact (rieszDenominator_verticalIntegrable hσ).norm.const_mul _
  refine ⟨fun n => (integrable_norm_iff (hc n).aestronglyMeasurable).mp (hnorm n), ?_⟩
  simp_rw [riesz_inverse_integrand_norm hy,integral_const_mul]
  exact (ha.norm.mul_left (y^(-σ))).mul_right _

lemma mellinInv_LSeries_riesz {σ y : ℝ} (hσ : 1≤σ) (hy : 0<y)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) y=
      ∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*y) := by
  obtain ⟨hi,hs⟩ := riesz_inverse_integrand_summable hσ hy a ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  simp only [mellinInv,smul_eq_mul,Complex.real_smul]
  simp only [LSeries,←tsum_div_const,←tsum_mul_left]
  rw [←he,←tsum_mul_left]
  apply tsum_congr
  intro n
  exact mellinInv_term_riesz hσ hy a n

noncomputable def rieszSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.Ioc 0 ⌊x⌋₊, a n*(1-(n:ℂ)/(x:ℂ))

lemma rieszKernel_tsum_eq {x : ℝ} (hx : 0<x) (a : ℕ → ℂ) :
    (∑' n : ℕ, if n=0 then 0 else a n*rieszKernel ((n:ℝ)*(1/x)))=rieszSum a x := by
  classical
  rw [tsum_eq_sum (s:=Finset.Ioc 0 ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn0,hnx⟩ := Finset.mem_Ioc.mp hn
    have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnx' : (n:ℝ)≤x := (Nat.le_floor_iff hx.le).mp hnx
    have hm0 : 0<(n:ℝ)*(1/x) := mul_pos hn0' (one_div_pos.mpr hx)
    have hm1 : (n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact (div_le_one hx).mpr hnx'
    rw [ite_eq_right (by omega : n≠0),rieszKernel,
      Set.indicator_of_mem (show (n:ℝ)*(1/x)∈Ioc (0:ℝ) 1 from ⟨hm0,hm1⟩)]
    push_cast
    ring
  · intro n hn
    by_cases hn0 : n=0
    · simp [hn0]
    have hnx : x<(n:ℝ) := by
      have hnot : ¬n≤⌊x⌋₊ := by intro h; exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,h⟩)
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff hx.le).mpr h))
    have hm1 : ¬(n:ℝ)*(1/x)≤1 := by rw [mul_one_div]; exact not_le.mpr ((lt_div_iff₀ hx).mpr (by simpa using hnx))
    rw [ite_eq_right hn0,rieszKernel,
      Set.indicator_of_notMem (show (n:ℝ)*(1/x)∉Ioc (0:ℝ) 1 from fun h => hm1 h.2),mul_zero]

lemma rieszSum_mellinInv {σ x : ℝ} (hσ : 1≤σ) (hx : 0<x)
    (a : ℕ → ℂ) (ha : LSeriesSummable a (σ:ℂ)) :
    mellinInv σ (fun s => LSeries a s/(s*(s+1))) (1/x)=rieszSum a x := by
  rw [mellinInv_LSeries_riesz hσ (one_div_pos.mpr hx) a ha,rieszKernel_tsum_eq hx]

open Complex Real Set MeasureTheory Filter Topology

end Vinogradov.Riesz
