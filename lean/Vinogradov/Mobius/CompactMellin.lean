/-
Selected generic analytic helpers from OpenAI's math repository (Apache 2.0).
Source pin: 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
The original proofs are retained with namespace changes, avoiding a dependency
on unrelated arithmetic modules for these generic analytic lemmas.
See HELPER-PROVENANCE.json for source files and excerpt boundaries.
-/
import Mathlib

noncomputable section
open Filter Asymptotics MeasureTheory Set Complex Metric
open scoped Topology Classical LSeries.notation ArithmeticFunction.Moebius

namespace Vinogradov.Mobius.CompactMellin

theorem inverse_mellin_analytic
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    exact hzero.isBigO.trans (isBigO_zero _ _)
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt

theorem compact_weight_mellin_convergent
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) : MellinConvergent W s := by
  have hlocal : LocallyIntegrableOn W (Set.Ioi (0 : ℝ)) :=
    hW.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : W =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact hsupp y (Or.inr hy)
  have hbotzero : W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    exact hsupp y (Or.inl hy.2.le)
  have htop : W =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : W =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem weighted_term_integrable
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hW : MellinConvergent W s) (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (a n * W ((n : ℝ) * t)))
      (Set.Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hscale : MellinConvergent
        (fun t : ℝ => W ((n : ℝ) * t)) s :=
      (MellinConvergent.comp_mul_left hnpos).mpr hW
    have hscaled := hscale.const_smul (a n)
    simpa only [MellinConvergent, smul_eq_mul, mul_assoc] using hscaled

theorem weighted_sum_continuousOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    ContinuousOn F (Set.Ioi (0 : ℝ)) := by
  intro t0 ht0
  have ht0pos : 0 < t0 := ht0
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / t0)
  have hNmul := mul_lt_mul_of_pos_right hN (by positivity : 0 < t0 / 2)
  have hNtwo : 2 < (N : ℝ) * (t0 / 2) := by
    have hdiv : (4 / t0) * (t0 / 2) = 2 := by
      field_simp
      ring
    rw [hdiv] at hNmul
    exact hNmul
  have hsumEq (u : ℝ) (hu : t0 / 2 ≤ u) :
      F u = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) := by
    have hupos : 0 < u := lt_of_lt_of_le (by positivity : 0 < t0 / 2) hu
    have htail (n : ℕ) (hn : n ∉ Finset.range N) :
        a n * W ((n : ℝ) * u) = 0 := by
      have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
      have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
      have hnu : 2 ≤ (n : ℝ) * u := by
        calc
          2 ≤ (N : ℝ) * (t0 / 2) := hNtwo.le
          _ ≤ (N : ℝ) * u :=
            mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) N)
          _ ≤ (n : ℝ) * u :=
            mul_le_mul_of_nonneg_right hnReal hupos.le
      simp [hsupp _ hnu]
    calc
      F u = ∑' n : ℕ, a n * W ((n : ℝ) * u) := (hF u hupos).tsum_eq.symm
      _ = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) :=
        tsum_eq_sum htail
  have hcontW : Continuous W := hW.continuous
  have hcontSum : Continuous
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    fun_prop
  have hevent : F =ᶠ[𝓝 t0]
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    filter_upwards [Ioi_mem_nhds (by linarith : t0 / 2 < t0)] with u hu
    exact hsumEq u hu.le
  exact (hcontSum.continuousAt.congr_of_eventuallyEq hevent).continuousWithinAt

theorem weighted_sum_inv_locallyIntegrableOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
    apply (weighted_sum_continuousOn_pos a W F hW hsupp hF).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi

private theorem weighted_norm_scale
    (a : ℂ) (W : ℝ → ℂ) (s : ℂ)
    (N t : ℝ) (hN : 0 < N) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * (a * W (N * t))‖ =
      (‖a‖ / N ^ (s.re - 1)) *
        ‖(N * t : ℂ) ^ (s - 1) * W (N * t)‖ := by
  have hNt : 0 < N * t := mul_pos hN ht
  have hNpow : 0 < N ^ (s.re - 1) := Real.rpow_pos_of_pos hN _
  rw [norm_mul, norm_mul, norm_mul]
  rw [← Complex.ofReal_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hNt]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.mul_rpow hN.le ht.le]
  field_simp

private theorem weighted_norm_integral
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
    ‖LSeries.term a s n‖ *
      (∫ u : ℝ in Set.Ioi 0,
        ‖(u : ℂ) ^ (s - 1) * W u‖) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0, LSeries.term_zero]
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let G : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (s - 1) * W u‖
    have hscale :
        (∫ t : ℝ in Set.Ioi 0,
          ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
          (‖a n‖ / (n : ℝ) ^ (s.re - 1)) *
            (∫ t : ℝ in Set.Ioi 0, G ((n : ℝ) * t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [G, Complex.ofReal_mul] using
        weighted_norm_scale (a n) W s n t hN ht
    rw [hscale, integral_comp_mul_left_Ioi G 0 hN]
    simp only [mul_zero, smul_eq_mul]
    have hpow : (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
        (n : ℝ) ^ s.re := by
      calc
        (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
            (n : ℝ) ^ (s.re - 1) * (n : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((s.re - 1) + 1) :=
          (Real.rpow_add hN (s.re - 1) 1).symm
        _ = (n : ℝ) ^ s.re := by congr 1; ring
    rw [LSeries.norm_term_eq]
    simp only [ite_eq_right hn, G]
    have hinv : ((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹ =
        ((n : ℝ) ^ s.re)⁻¹ := by
      rw [← mul_inv_rev, mul_comm, hpow]
    simp only [div_eq_mul_inv]
    calc
      ‖a n‖ * ((n : ℝ) ^ (s.re - 1))⁻¹ *
          ((n : ℝ)⁻¹ *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖)) =
          (‖a n‖ * (((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹)) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by ring
      _ = (‖a n‖ * ((n : ℝ) ^ s.re)⁻¹) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by rw [hinv]

theorem weighted_terms_fubini
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hlsum : LSeriesSummable a s) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) := by
  let C : ℝ := ∫ u : ℝ in Set.Ioi 0,
    ‖(u : ℂ) ^ (s - 1) * W u‖
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term a s n‖) := hlsum.norm
  have hsum : Summable (fun n : ℕ => ‖LSeries.term a s n‖ * C) :=
    hnorm.mul_right C
  exact hsum.congr (fun n => (weighted_norm_integral a ha0 W s n).symm)

theorem mellin_weighted_sum
    (a : ℕ → ℂ) (W F : ℝ → ℂ) (s : ℂ)
    (ha0 : a 0 = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) =
      mellin W s * LSeries a s := by
  have hterm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        mellin W s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hscale := mellin_comp_mul_left W s hnpos
      have hmul : mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s =
          a n * mellin (fun t : ℝ => W ((n : ℝ) * t)) s := by
        simpa only [smul_eq_mul] using
          (mellin_const_smul (fun t : ℝ => W ((n : ℝ) * t)) s (a n))
      change mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s = _
      rw [hmul, hscale, LSeries.term_of_ne_zero hn]
      simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
  have hsum :
      (∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
    integral_tsum_of_summable_integral_norm hint hsumint
  have hseries :
      (∑' n : ℕ, mellin W s * LSeries.term a s n) =
        mellin W s * LSeries a s := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (mellin W s) |>.tsum_eq
  calc
    mellin (fun D : ℝ => F D⁻¹) (-s) = mellin F s := by
      simpa using mellin_comp_inv F (-s)
    _ = ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (s - 1) * F t =
        ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))
      rw [← (hF t ht).tsum_eq]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := hsum.symm
    _ = ∑' n : ℕ, mellin W s * LSeries.term a s n := by simp_rw [hterm]
    _ = mellin W s * LSeries a s := hseries

theorem weighted_sum_zero_of_large_t
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (t : ℝ) (ht : 2 ≤ t) : F t = 0 := by
  have hterm (n : ℕ) : a n * W ((n : ℝ) * t) = 0 := by
    by_cases hn : n = 0
    · simp [hn, ha0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnt : 2 ≤ (n : ℝ) * t := by
        calc
          2 ≤ t := ht
          _ = (1 : ℝ) * t := by ring
          _ ≤ (n : ℝ) * t :=
            mul_le_mul_of_nonneg_right hn1 (by linarith)
      simp [hW _ hnt]
  have hzero : HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact (hF t (lt_of_lt_of_le (by norm_num) ht)).unique hzero

theorem weighted_sum_zero_near_small_D
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
  have hDpos : 0 < D := hD.1
  have hDsmall : D < 1 / 2 := hD.2
  have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
  have hinv : 2 ≤ D⁻¹ := by
    rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
    nlinarith
  exact weighted_sum_zero_of_large_t a ha0 W F hW hF D⁻¹ hinv

theorem compact_weight_mellin_analytic
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ) :
    AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re} := by
  let A : ℝ → ℂ := fun D => W D⁻¹
  have hcont : ContinuousOn A (Set.Ioi (0 : ℝ)) := by
    have hcontW : ContinuousOn W Set.univ := hW.continuous.continuousOn
    apply hcontW.comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    simp
  have hlocal : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
    have hDpos : 0 < D := hD.1
    have hDsmall : D < 1 / 2 := hD.2
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
    have hinv : 2 ≤ D⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inr hinv)
  have hzeroTop : A =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right hD hDinvpos.le
    have hinv : D⁻¹ ≤ 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inl hinv)
  have htop : A =O[atTop] (fun D : ℝ => D ^ σ) :=
    hzeroTop.isBigO.trans (isBigO_zero _ _)
  have hM := inverse_mellin_analytic A σ hlocal htop hzero
  simpa only [A, mellin_comp_inv, neg_neg] using hM


end Vinogradov.Mobius.CompactMellin
