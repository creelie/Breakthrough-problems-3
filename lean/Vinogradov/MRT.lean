import Mathlib

/-!
# Growth of nonprincipal Dirichlet L-functions in the right half-plane

For a nonprincipal character `χ` modulo `q` and `re s > 0`,
`‖L(s, χ)‖ ≤ q ‖s‖ / re s`.

The proofs in this file are taken, with namespace changes only, from
`OAI/NumberTheory/TwoPoint/ShortIntervals/MRTCharacter{Sums,Abel,Continuation}.lean`
of OpenAI's `math` repository (Apache License 2.0).
-/

namespace Vinogradov.MRT

/-! Explicit modulus dependence in nonprincipal character partial sums,
and the resulting exact Abel integral on its initial half-plane. -/


open Finset Filter Asymptotics MeasureTheory
open scoped Classical Topology

lemma mrt_character_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (k n : ℕ) :
    χ ((q*k+n:ℕ):ZMod q)=χ (n:ZMod q) := by
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]

lemma mrt_character_period_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (∑ n∈range q,χ (n:ZMod q))=0 := by
  have hs := χ.sum_eq_zero_of_ne_one hχ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    calc
      _ = ∑ n : Fin (q+1),χ (n.val:ZMod (q+1)) :=
        (Fin.sum_univ_eq_sum_range (fun n : ℕ => χ (n:ZMod (q+1))) (q+1)).symm
      _ = ∑ n : ZMod (q+1),χ n := by
        apply sum_congr rfl
        intro n _
        exact congrArg χ (ZMod.natCast_zmod_val (n := q+1) n)
      _ = 0 := hs

lemma mrt_character_full_periods {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (k : ℕ) :
    (∑ n∈range (q*k),χ (n:ZMod q))=0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,sum_range_add,ih,zero_add]
    simp_rw [mrt_character_shift]
    exact mrt_character_period_sum χ hχ

lemma mrt_character_prefix_remainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈range N,χ (n:ZMod q))=∑ n∈range (N%q),χ (n:ZMod q) := by
  have hN : N=q*(N/q)+N%q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  conv_lhs => rw [hN,sum_range_add,mrt_character_full_periods χ hχ,zero_add]
  exact sum_congr rfl (fun n _ => mrt_character_shift χ (N/q) n)

theorem mrt_character_prefix_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈range N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_prefix_remainder χ hχ]
  calc
    _ ≤ ∑ n∈range (N%q),‖χ (n:ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range (N%q),(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = (N%q:ℕ) := by simp
    _ ≤ (q:ℝ) := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

lemma mrt_character_Icc_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈Icc 1 N,χ (n:ZMod q))=∑ n∈range (N+1),χ (n:ZMod q) := by
  have hq : q≠1 := by
    intro hq
    subst q
    apply hχ
    ext n
    have hn : n=(1:ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  let : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  rw [Nat.range_succ_eq_Icc_zero]
  have hset : Icc 1 N=Ioc 0 N := by ext n; simp; omega
  rw [hset,←add_sum_Ioc_eq_sum_Icc (Nat.zero_le N),Nat.cast_zero,
    MulChar.map_zero χ,zero_add]

theorem mrt_character_Icc_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈Icc 1 N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_Icc_eq χ hχ]
  exact mrt_character_prefix_norm χ hχ (N+1)

lemma mrt_character_sum_bigO {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (fun N : ℕ => ∑ n∈Icc 1 N,χ (n:ZMod q)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^(0:ℝ)) := by
  refine isBigO_iff.mpr ⟨(q:ℝ),Eventually.of_forall (fun N => ?_)⟩
  simpa only [Real.rpow_zero,norm_one,mul_one] using mrt_character_Icc_norm χ hχ N

theorem mrt_character_LFunction_Abel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) {s : ℂ} (hs : 1<s.re) :
    DirichletCharacter.LFunction χ s =
      s*∫ t in Set.Ioi (1:ℝ),
        (∑ n∈Icc 1 ⌊t⌋₊,χ (n:ZMod q))*(t:ℂ)^(-(s+1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_eq_mul_integral (fun n => χ (n:ZMod q)) (by norm_num : (0:ℝ)≤0)
    (by linarith : (0:ℝ)<s.re) (χ.LSeriesSummable_of_one_lt_re hs)
    (mrt_character_sum_bigO χ hχ)

/-! Abel-integral bounds for every nonprincipal character, retaining the
explicit modulus q in the bound q * norm(s) / re(s). -/


open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterSummatory (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod q)

noncomputable def mrtCharacterAbelKernel (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  mrtCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))

noncomputable def mrtCharacterAbelIntegral (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t

omit [NeZero q] in
lemma mrtCharacterSummatory_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterSummatory χ) := by
  exact (measurable_from_nat (f := fun N => ∑ n ∈ Icc 1 N, χ (n : ZMod q))).comp
    Nat.measurable_floor

lemma mrtCharacterSummatory_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterSummatory χ t‖ ≤ (q : ℝ) :=
  mrt_character_Icc_norm χ hχ ⌊t⌋₊

omit [NeZero q] in
lemma mrtCharacterAbelKernel_measurable (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable (mrtCharacterAbelKernel χ s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact (mrtCharacterSummatory_measurable χ).aestronglyMeasurable.mul
    (hpow.aestronglyMeasurable measurableSet_Ioi)

lemma mrtCharacterAbelKernel_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) * t ^ (-(s.re + 1)) := by
  rw [mrtCharacterAbelKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.neg_re,
    Complex.add_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (mrtCharacterSummatory_norm χ hχ t)
    (Real.rpow_nonneg (zero_lt_one.trans ht).le _)

theorem mrtCharacterAbelKernel_integrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (mrtCharacterAbelKernel χ s) (Set.Ioi (1 : ℝ)) := by
  have hmajor : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul (q : ℝ)
  refine hmajor.mono' (mrtCharacterAbelKernel_measurable χ s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mrtCharacterAbelKernel_norm_le χ hχ s ht

lemma mrtCharacterAbelKernel_integral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul (q : ℝ))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mrtCharacterAbelKernel_norm_le χ hχ s ht
    _ = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [ne_of_gt hs]
      ring

theorem mrtCharacterAbelIntegral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mrtCharacterAbelIntegral χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [mrtCharacterAbelIntegral, norm_mul]
  calc
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
      mul_le_mul_of_nonneg_left (mrtCharacterAbelKernel_integral_norm χ hχ hs) (norm_nonneg s)
    _ = _ := by ring

theorem mrtCharacterAbelIntegral_eq_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s :=
  (mrt_character_LFunction_Abel χ hχ hs).symm

/-! The nonprincipal character Abel integral agrees with the existing
L-function throughout re(s)>0, with explicit modulus dependence. -/


open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology


noncomputable def mrtCharacterAbelInput (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (mrtCharacterSummatory χ)

omit [NeZero q] in
lemma mrtCharacterAbelInput_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterAbelInput χ) :=
  (mrtCharacterSummatory_measurable χ).indicator measurableSet_Ioi

lemma mrtCharacterAbelInput_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterAbelInput χ t‖ ≤ (q : ℝ) := by
  by_cases ht : 1 < t
  · simpa only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_left ht] using
      mrtCharacterSummatory_norm χ hχ t
  · simp only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_right ht, norm_zero]
    exact Nat.cast_nonneg q

lemma mrtCharacterAbelInput_locallyIntegrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    LocallyIntegrableOn (mrtCharacterAbelInput χ) (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (q : ℝ)).mono
    (mrtCharacterAbelInput_measurable χ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa using mrtCharacterAbelInput_norm χ hχ t

lemma mrtCharacterAbelInput_bigO_atTop (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    mrtCharacterAbelInput χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (q : ℝ) (Eventually.of_forall fun t => ?_)
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using mrtCharacterAbelInput_norm χ hχ t

omit [NeZero q] in
lemma mrtCharacterAbelInput_bigO_zero (χ : DirichletCharacter ℂ q) (b : ℝ) :
    mrtCharacterAbelInput χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hnot : t ∉ Set.Ioi (1 : ℝ) := by change ¬1 < t; linarith
  simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hnot, norm_zero, zero_mul, le_refl]

omit [NeZero q] in
lemma mrtCharacterAbelIntegral_eq_mellin (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mrtCharacterAbelIntegral χ s = s * mellin (mrtCharacterAbelInput χ) (-s) := by
  unfold mrtCharacterAbelIntegral mellin
  congr 1
  have heq : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • mrtCharacterAbelInput χ t) =
      (Set.Ioi (1 : ℝ)).indicator (mrtCharacterAbelKernel χ s) := by
    funext t
    by_cases ht : 1 < t
    · simp only [mrtCharacterAbelInput, Set.indicator_apply, Set.mem_Ioi, ite_eq_left ht,
        smul_eq_mul, mrtCharacterAbelKernel]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · have hn : t ∉ Set.Ioi (1 : ℝ) := ht
      simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hn, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.mpr (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) from
    fun t ht => lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)]

theorem mrtCharacterAbelIntegral_differentiableAt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (mrtCharacterAbelIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (mrtCharacterAbelInput χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (mrtCharacterAbelInput_locallyIntegrable χ hχ) (mrtCharacterAbelInput_bigO_atTop χ hχ)
      (b := -s.re - 1)
    · simpa only [Complex.neg_re] using neg_neg_of_pos hs
    · exact mrtCharacterAbelInput_bigO_zero χ _
    · simp only [Complex.neg_re]
      linarith
  have heq : mrtCharacterAbelIntegral χ = fun z => z * mellin (mrtCharacterAbelInput χ) (-z) :=
    funext (mrtCharacterAbelIntegral_eq_mellin χ)
  rw [heq]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- The bounded-partial-sum integral is the existing L-function on the
entire half-plane of convergence of that integral. -/
theorem mrtCharacterAbelIntegral_eq_LFunction_of_pos (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (mrtCharacterAbelIntegral χ) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (mrtCharacterAbelIntegral_differentiableAt χ hχ hz).differentiableWithinAt
  have heq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] mrtCharacterAbelIntegral χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact (mrtCharacterAbelIntegral_eq_LFunction χ hχ hz).symm
  exact (hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected
    (show (2 : ℂ) ∈ U by change 0 < (2 : ℂ).re; norm_num) heq hs).symm

theorem mrt_character_LFunction_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [← mrtCharacterAbelIntegral_eq_LFunction_of_pos χ hχ hs]
  exact mrtCharacterAbelIntegral_norm χ hχ hs

theorem mrt_character_LFunction_norm_halfPlane (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (2 * q : ℝ) * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  calc
    _ ≤ (q : ℝ) * ‖s‖ / s.re := mrt_character_LFunction_norm_le χ hχ hs0
    _ ≤ (q : ℝ) * ‖s‖ / (1/2) :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg q) (norm_nonneg s))
        (by norm_num) hs
    _ = _ := by ring

end Vinogradov.MRT
