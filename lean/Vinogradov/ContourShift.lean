import Mathlib

/-!
# Shifting a vertical line integral across a strip

If `f` is holomorphic on the closed strip `a ≤ re z ≤ b`, integrable on both boundary lines
and of at most exponential growth `B exp (A |t|)` in the strip, then the integrals of `f`
over the two boundary lines agree.

The proof (a Gaussian regulator `exp (ε z²)` followed by the rectangle theorem) is taken
from `OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean`,
`OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean` and
`OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean` of OpenAI's `math` repository
(Apache License 2.0).
-/

namespace Vinogradov.ContourShift

open MeasureTheory Filter Set
open scoped Topology Classical
theorem x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring


theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm


lemma gaussian_regulator_norm (ε σ t : ℝ) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖=Real.exp (ε*(σ^2-t^2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma gaussian_regulator_norm_le (ε σ t : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖≤Real.exp (σ^2) := by
  rw [gaussian_regulator_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg σ,sq_nonneg t,mul_nonneg hε0 (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg σ)]

noncomputable def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma gaussianRegulatorSequence_pos (n : ℕ) : 0<gaussianRegulatorSequence n := by
  unfold gaussianRegulatorSequence
  positivity

lemma gaussianRegulatorSequence_le_one (n : ℕ) : gaussianRegulatorSequence n≤1 := by
  unfold gaussianRegulatorSequence
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma gaussianRegulatorSequence_tendsto : Tendsto gaussianRegulatorSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem gaussian_regulator_integral_tendsto (g : ℝ→ℂ) (hg : Integrable g) (σ : ℝ) :
    Tendsto (fun n : ℕ=>∫t : ℝ,
      Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)*g t)
      atTop (𝓝 (∫t : ℝ,g t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ=>Real.exp (σ^2)*‖g t‖)
  · intro n
    have hc : Continuous (fun t : ℝ=>
        Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    exact Filter.Eventually.of_forall (fun t=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (gaussian_regulator_norm_le _ σ t (gaussianRegulatorSequence_pos n).le
          (gaussianRegulatorSequence_le_one n)) (norm_nonneg _))
  · filter_upwards with t
    have hε : Tendsto (fun n : ℕ=>(gaussianRegulatorSequence n:ℂ)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp gaussianRegulatorSequence_tendsto
    have he := (Complex.continuous_exp.tendsto 0).comp
      (by simpa only [zero_mul] using hε.mul_const (((σ:ℂ)+t*Complex.I)^2))
    simpa only [Function.comp_def,Complex.exp_zero,one_mul] using he.mul_const (g t)

lemma gaussian_le_inverse_quadratic (c t:ℝ) (hc:0<c) :
    Real.exp (-c*t^2)≤(1+2/c)/(1+t^2) := by
  have h0:Real.exp (-c*t^2)≤1:=by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  have h1:t^2*Real.exp (-c*t^2)≤2/c:=by
    have hm:=gaussian_moment_term_bound (t^2) c (sq_nonneg t) hc
    have he:Real.exp (-(c*t^2/2))≤1:=by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    exact hm.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num) hc.le))
  apply (le_div_iff₀ (by positivity : 0<1+t^2)).mpr
  nlinarith

lemma linear_height_young (A ε t:ℝ) (hε:0<ε) :
    A*|t|≤ε*t^2/2+A^2/(2*ε) := by
  have hs:0≤ε^2*t^2-2*ε*A*|t|+A^2:=by
    calc
      0≤(ε*|t|-A)^2:=sq_nonneg _
      _=ε^2*t^2-2*ε*A*|t|+A^2:=by rw [sub_sq,mul_pow,sq_abs];ring
  apply le_of_mul_le_mul_left (a := 2*ε) ?_
    (mul_pos (by norm_num : (0:ℝ)<2) hε)
  calc
    2*ε*(A*|t|)≤ε^2*t^2+A^2:=by nlinarith [hs]
    _=2*ε*(ε*t^2/2+A^2/(2*ε)):=by field_simp

theorem gaussian_regulator_strip_bound (a b A B ε:ℝ) (hB:0≤B) (hε:0<ε)
    (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|))
    (σ t:ℝ) (hσ:σ∈Set.Icc a b) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤
      (B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε))/(1+t^2) := by
  let R:ℝ:=max |a| |b|
  have hR:0≤R:=le_trans (abs_nonneg a) (le_max_left _ _)
  have hsabs:|σ|≤R:=abs_le_max_abs_abs hσ.1 hσ.2
  have hs:σ^2≤R^2:=by
    calc
      _=|σ|^2:=(sq_abs σ).symm
      _≤R^2:=pow_le_pow_left₀ (abs_nonneg σ) hsabs 2
  have hre:((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2).re=ε*(σ^2-t^2):=by
    simp [pow_two,Complex.mul_re,Complex.mul_im]

  have hE:ε*(σ^2-t^2)+A*|t|≤
      (ε*R^2+A^2/(2*ε))-(ε/2)*t^2:=by
    have hy:=linear_height_young A ε t hε
    nlinarith
  have hg:=gaussian_le_inverse_quadratic (ε/2) t (by positivity)
  have hg':Real.exp (-(ε/2)*t^2)≤(1+4/ε)/(1+t^2):=by
    convert hg using 1 ;field_simp ;ring
  rw [norm_mul,Complex.norm_exp,hre]
  calc
    _≤Real.exp (ε*(σ^2-t^2))*(B*Real.exp (A*|t|)):=
      mul_le_mul_of_nonneg_left (hf σ hσ t) (Real.exp_pos _).le
    _=B*Real.exp (ε*(σ^2-t^2)+A*|t|):=by rw [Real.exp_add];ring
    _≤B*Real.exp ((ε*R^2+A^2/(2*ε))-(ε/2)*t^2):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hB
    _=(B*Real.exp (ε*R^2+A^2/(2*ε)))*Real.exp (-(ε/2)*t^2):=by
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,neg_mul]
      ring
    _≤(B*Real.exp (ε*R^2+A^2/(2*ε)))*((1+4/ε)/(1+t^2)):=
      mul_le_mul_of_nonneg_left hg' (mul_nonneg hB (Real.exp_pos _).le)
    _=_:=by dsimp only [R];ring

theorem gaussian_regulator_strip_decay (a b A B ε:ℝ) (_hab:a≤b) (_hA:0≤A)
    (hB:0≤B) (hε:0<ε) (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|)) :
    ∃K:ℝ,0≤K ∧ ∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤K/(1+t^2) := by
  refine ⟨B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε),by positivity,?_⟩
  intro σ hσ t
  exact gaussian_regulator_strip_bound a b A B ε hB hε f hf σ t hσ

theorem integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by
  let F : ℕ→ℂ→ℂ := fun n z=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)*f z
  have hreg (n : ℕ) : Continuous (fun z : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)) := by
    fun_prop
  have hint (n : ℕ) (σ : ℝ) (hσ : Integrable (fun t : ℝ=>f ((σ:ℂ)+t*Complex.I))) :
      Integrable (fun t : ℝ=>F n ((σ:ℂ)+t*Complex.I)) := by
    apply hσ.bdd_mul (c:=Real.exp (σ^2))
    · exact ((hreg n).comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t=>gaussian_regulator_norm_le _ σ t
        (gaussianRegulatorSequence_pos n).le (gaussianRegulatorSequence_le_one n))
  have heq (n : ℕ) :
      (∫t : ℝ,F n ((a:ℂ)+t*Complex.I))=∫t : ℝ,F n ((b:ℂ)+t*Complex.I) := by
    obtain ⟨K,hK,hdec⟩ := gaussian_regulator_strip_decay a b A B
      (gaussianRegulatorSequence n) hab hA hB (gaussianRegulatorSequence_pos n) f hbound
    apply integral_eq_of_strip_decay (F n) a b K hab
    · intro z hza hzb
      have hg : Differentiable ℂ (fun w : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*w^2)) := by
        fun_prop
      exact hg.differentiableAt.mul (hdiff z hza hzb)
    · exact hint n a ha
    · exact hint n b hb
    · exact hdec
  have hleft := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)) ha a
  have hright := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)) hb b
  change Tendsto (fun n=>∫t : ℝ,F n ((a:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((a:ℂ)+t*Complex.I))) at hleft
  change Tendsto (fun n=>∫t : ℝ,F n ((b:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((b:ℂ)+t*Complex.I))) at hright
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end Vinogradov.ContourShift
