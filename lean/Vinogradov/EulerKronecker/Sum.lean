/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The sum of `L'/L(1, χ)` over the nonprincipal characters modulo a prime `q`.
-/
import Mathlib
import Vinogradov.EulerKronecker.LogDeriv
import Vinogradov.EulerKronecker.Dyadic

namespace Vinogradov.EulerKronecker
open Complex Real Set MeasureTheory Filter Topology Asymptotics
open Vinogradov.Riesz
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- The real Riesz sum `∑_{n ≤ x} b n (1 - n/x)`. -/
noncomputable def rieszSumR (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, b n * (1 - n / x)

lemma rieszSum_ofReal (b : ℕ → ℝ) (x : ℝ) :
    rieszSum (fun n => (b n : ℂ)) x = (rieszSumR b x : ℂ) := by
  unfold rieszSum rieszSumR; push_cast; rfl

lemma rieszSum_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℂ) (x : ℝ) :
    ∑ i ∈ s, rieszSum (a i) x = rieszSum (fun n => ∑ i ∈ s, a i n) x := by
  unfold rieszSum; rw [Finset.sum_comm]; simp only [Finset.sum_mul]

/-- The coefficients of `∑_{χ ≠ 1} χ Λ` modulo a prime `q`. -/
noncomputable def Tc (q n : ℕ) : ℝ :=
  ((if (n : ZMod q) = 1 then (q - 1 : ℝ) else 0) - (if n.Coprime q then 1 else 0)) * Λ n

lemma sum_chars_ne_one {q : ℕ} [NeZero q] (hq : q.Prime) (n : ℕ) :
    ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), (↗χ * ↗Λ) n = (Tc q n : ℂ) := by
  simp only [Pi.mul_apply]
  rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    DirichletCharacter.sum_characters_eq, Nat.totient_prime hq]
  unfold Tc
  by_cases hu : n.Coprime q
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hu)]
    simp only [eq_true hu, ↓reduceIte]
    split_ifs <;> push_cast [Nat.cast_sub hq.one_le] <;> ring
  · rw [MulChar.map_nonunit _ (fun h => hu ((ZMod.isUnit_iff_coprime n q).mp h))]
    simp only [eq_false hu, ↓reduceIte]
    split_ifs <;> push_cast [Nat.cast_sub hq.one_le] <;> ring

lemma mellinConvergent_rieszSum (a : ℕ → ℂ) {θ K : ℝ} (hθ : θ < 1)
    (hR : ∀ x : ℝ, 1 ≤ x → ‖rieszSum a x‖ ≤ K * x ^ θ) :
    MellinConvergent (rieszSum a) (-1) := by
  apply mellinConvergent_of_isBigO_rpow (a := -θ) (b := -2)
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

lemma cpow_smul_ofReal {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (t : ℂ) ^ ((-1 : ℂ) - 1) • (r : ℂ) = ((t ^ (-2 : ℝ) * r : ℝ) : ℂ) := by
  rw [show (-1 : ℂ) - 1 = ((-2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht,
    smul_eq_mul, ← Complex.ofReal_mul]

/-- For `q` prime, `∑_{χ ≠ 1} -L'/L(1, χ) = 2 ∫_0^∞ t^{-2} T(t) dt` with `T` the real Riesz sum
of `Tc q`. -/
lemma sum_neg_logDeriv_eq {q : ℕ} [NeZero q] (hq : q.Prime) {θ K : ℝ} (hθ : θ < 1)
    (hK : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ θ) :
    ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
      2 * ((∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t : ℝ) : ℂ) := by
  set s := Finset.univ.erase (1 : DirichletCharacter ℂ q) with hs
  have hne : ∀ χ ∈ s, χ ≠ 1 := fun χ hχ => Finset.ne_of_mem_erase hχ
  calc ∑ χ ∈ s, -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
      = ∑ χ ∈ s, 2 * mellin (rieszSum (↗χ * ↗Λ)) (-1) :=
        Finset.sum_congr rfl (fun χ hχ => neg_logDeriv_one_eq χ (hne χ hχ) hθ (hK χ (hne χ hχ)))
    _ = 2 * mellin (fun t => ∑ χ ∈ s, rieszSum (↗χ * ↗Λ) t) (-1) := by
        rw [← Finset.mul_sum]
        congr 1
        unfold mellin
        rw [← integral_finsetSum _ (fun χ hχ =>
          mellinConvergent_rieszSum _ hθ (hK χ (hne χ hχ)))]
        congr with t
        rw [Finset.smul_sum]
    _ = 2 * mellin (fun t => (rieszSumR (Tc q) t : ℂ)) (-1) := by
        congr with t
        rw [rieszSum_finset_sum, ← rieszSum_ofReal]
        congr with n
        exact sum_chars_ne_one hq n
    _ = 2 * ((∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t : ℝ) : ℂ) := by
        congr 1
        unfold mellin
        rw [← integral_complex_ofReal]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact cpow_smul_ofReal (le_of_lt ht) _


lemma rieszSumR_Tc_eq {q : ℕ} [NeZero q] (hq : q.Prime) (x : ℝ) :
    (rieszSumR (Tc q) x : ℂ) =
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), rieszSum (↗χ * ↗Λ) x := by
  rw [rieszSum_finset_sum, ← rieszSum_ofReal]
  congr with n
  exact (sum_chars_ne_one hq n).symm

lemma card_erase_one_le {q : ℕ} [NeZero q] :
    ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) ≤ q := by
  have h1 := Finset.card_erase_le (s := Finset.univ) (a := (1 : DirichletCharacter ℂ q))
  have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h3 := Nat.totient_le q
  rw [h2] at h1
  exact_mod_cast h1.trans h3

/-- The real Riesz sum of `Tc q` is at most `q K x^θ` when every `χ ≠ 1` satisfies the bound
`K x^θ`. -/
lemma abs_rieszSumR_Tc_le {q : ℕ} [NeZero q] (hq : q.Prime) {θ K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ θ) {x : ℝ} (hx : 1 ≤ x) :
    |rieszSumR (Tc q) x| ≤ q * K * x ^ θ := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, rieszSumR_Tc_eq hq]
  have hKx : 0 ≤ K * x ^ θ := mul_nonneg hK0 (Real.rpow_nonneg (by linarith) _)
  calc ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), rieszSum (↗χ * ↗Λ) x‖
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ‖rieszSum (↗χ * ↗Λ) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), K * x ^ θ :=
        Finset.sum_le_sum (fun χ hχ => hK χ (Finset.ne_of_mem_erase hχ) x hx)
    _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * (K * x ^ θ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ q * (K * x ^ θ) := mul_le_mul_of_nonneg_right (card_erase_one_le (q := q)) hKx
    _ = q * K * x ^ θ := by ring

lemma rieszSumR_eq_zero_of_lt_one (b : ℕ → ℝ) {x : ℝ} (hx : x < 1) : rieszSumR b x = 0 := by
  unfold rieszSumR
  rw [Nat.floor_eq_zero.mpr hx]
  simp

lemma integrableOn_rieszSumR_Tc {q : ℕ} {θ M : ℝ} (hθ : θ < 1)
    (hT : ∀ t : ℝ, 1 ≤ t → |rieszSumR (Tc q) t| ≤ M * t ^ θ) :
    IntegrableOn (fun t => t ^ (-2 : ℝ) * rieszSumR (Tc q) t) (Ioi 0) := by
  have hc := mellinConvergent_rieszSum (fun n => (Tc q n : ℂ)) hθ (K := M) (fun x hx => by
    rw [rieszSum_ofReal, Complex.norm_real, Real.norm_eq_abs]; exact hT x hx)
  have hre : IntegrableOn (fun t : ℝ => RCLike.re ((t : ℂ) ^ ((-1 : ℂ) - 1) •
      rieszSum (fun n => (Tc q n : ℂ)) t)) (Ioi 0) := Integrable.re hc
  refine hre.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only
  rw [rieszSum_ofReal, cpow_smul_ofReal (le_of_lt ht)]
  exact Complex.ofReal_re _

/-- The weight of `n ≡ 1 (mod q)`. -/
noncomputable def wq (q n : ℕ) : ℝ := if (n : ZMod q) = 1 then Λ n else 0

lemma wq_nonneg (q n : ℕ) : 0 ≤ wq q n := by
  unfold wq
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

lemma Tc_le {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : Tc q n ≤ (q - 1) * wq q n := by
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  unfold Tc wq
  split_ifs <;> nlinarith

lemma neg_Tc_le {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : -Tc q n ≤ Λ n := by
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  unfold Tc
  split_ifs <;> nlinarith

lemma one_sub_div_mem {n : ℕ} {t : ℝ} (ht : 0 < t) (hn : n ∈ Finset.Ioc 0 ⌊t⌋₊) :
    0 ≤ 1 - (n : ℝ) / t ∧ 1 - (n : ℝ) / t ≤ 1 := by
  have hnt : (n : ℝ) ≤ t := (Nat.le_floor_iff ht.le).mp (Finset.mem_Ioc.mp hn).2
  constructor
  · rw [sub_nonneg, div_le_one ht]; exact hnt
  · have : 0 ≤ (n : ℝ) / t := by positivity
    linarith

lemma neg_rieszSumR_le_psi {q : ℕ} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t) :
    -rieszSumR (Tc q) t ≤ Chebyshev.psi t := by
  unfold rieszSumR Chebyshev.psi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨h0, h1⟩ := one_sub_div_mem ht hn
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  calc -(Tc q n * (1 - n / t)) = (-Tc q n) * (1 - n / t) := by ring
    _ ≤ Λ n * (1 - n / t) := mul_le_mul_of_nonneg_right (neg_Tc_le hq n) h0
    _ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left h1 hΛ
    _ = Λ n := mul_one _

lemma indicator_rpow_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t :=
  indicator_nonneg (fun _ ha => Real.rpow_nonneg
    (le_trans (Nat.cast_nonneg n) (le_of_lt ha)) _) t

lemma rpow_mul_rieszSumR_le {q : ℕ} (hq : 1 ≤ q) (Y : ℕ) {t : ℝ} (ht : 0 < t)
    (htY : t ≤ Y) :
    t ^ (-2 : ℝ) * rieszSumR (Tc q) t ≤
      (q - 1) * ∑ n ∈ Finset.Ioc 0 Y,
        wq q n * (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t := by
  have hp : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht.le _
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  unfold rieszSumR
  rw [Finset.mul_sum, Finset.mul_sum]
  have hsub : Finset.Ioc 0 ⌊t⌋₊ ⊆ Finset.Ioc 0 Y := by
    apply Finset.Ioc_subset_Ioc le_rfl
    calc ⌊t⌋₊ ≤ ⌊(Y : ℝ)⌋₊ := Nat.floor_le_floor htY
      _ = Y := Nat.floor_natCast Y
  calc ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, t ^ (-2 : ℝ) * (Tc q n * (1 - n / t))
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊,
          (q - 1) * (wq q n * (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨h0, h1⟩ := one_sub_div_mem ht hn
        have hw := wq_nonneg q n
        by_cases hnt : (n : ℝ) < t
        · rw [indicator_of_mem (show t ∈ Ioi (n : ℝ) from hnt)]
          calc t ^ (-2 : ℝ) * (Tc q n * (1 - n / t))
              ≤ t ^ (-2 : ℝ) * (((q - 1) * wq q n) * (1 - n / t)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Tc_le hq n) h0) hp
            _ ≤ t ^ (-2 : ℝ) * (((q - 1) * wq q n) * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h1 (mul_nonneg hq1 hw)) hp
            _ = (q - 1) * (wq q n * t ^ (-2 : ℝ)) := by ring
        · have hle : (n : ℝ) ≤ t := (Nat.le_floor_iff ht.le).mp (Finset.mem_Ioc.mp hn).2
          have hnt' : (n : ℝ) = t := le_antisymm hle (not_lt.mp hnt)
          have h1' : 1 - (n : ℝ) / t = 0 := by rw [hnt', div_self ht.ne', sub_self]
          rw [h1', mul_zero, mul_zero]
          exact mul_nonneg hq1 (mul_nonneg hw (indicator_rpow_nonneg n t))
    _ ≤ ∑ n ∈ Finset.Ioc 0 Y,
          (q - 1) * (wq q n * (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        exact mul_nonneg hq1 (mul_nonneg (wq_nonneg q n) (indicator_rpow_nonneg n t))

lemma integral_indicator_rpow {n : ℕ} (hn : 0 < n) :
    ∫ t in Ioi (0 : ℝ), (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Ioi_subset_Ioi hn0.le),
    integral_Ioi_rpow_of_lt (by norm_num) hn0]
  norm_num [Real.rpow_neg_one]

lemma integrableOn_indicator_rpow (n : ℕ) (hn : 0 < n) :
    Integrable (fun t : ℝ => (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t)
      (volume.restrict (Ioi 0)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine Integrable.restrict ?_
  exact (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hn0)

/-- Upper bound for the Mellin integral of `Tc q`. -/
theorem integral_rieszSumR_le {q : ℕ} (hq : 1 ≤ q) {Y : ℕ} (hY : 1 ≤ Y) {θ M : ℝ} (hθ : θ < 1)
    (hM : 0 ≤ M) (hT : ∀ t : ℝ, (Y : ℝ) < t → |rieszSumR (Tc q) t| ≤ M * t ^ θ)
    (hint : IntegrableOn (fun t => t ^ (-2 : ℝ) * rieszSumR (Tc q) t) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t ≤
      (q - 1) * ∑ n ∈ Finset.Ioc 0 Y, (if (n : ZMod q) = 1 then Λ n / n else 0) +
        M * (Y : ℝ) ^ (θ - 1) / (1 - θ) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  set g1 : ℝ → ℝ := fun t => (q - 1) * ∑ n ∈ Finset.Ioc 0 Y,
      wq q n * (Ioi (n : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) t with hg1
  set g2 : ℝ → ℝ := (Ioi (Y : ℝ)).indicator (fun t => M * t ^ (θ - 2)) with hg2
  have hq1 : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have i1 : Integrable g1 (volume.restrict (Ioi 0)) := by
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ (fun n hn => ?_)
    exact (integrableOn_indicator_rpow n (Finset.mem_Ioc.mp hn).1).const_mul _
  have i2 : Integrable g2 (volume.restrict (Ioi 0)) := by
    refine Integrable.restrict ?_
    exact (integrable_indicator_iff measurableSet_Ioi).mpr
      ((integrableOn_Ioi_rpow_of_lt (by linarith) hY0).const_mul M)
  have hg1n : ∀ t, 0 ≤ g1 t := fun t => mul_nonneg hq1 (Finset.sum_nonneg (fun n _ =>
    mul_nonneg (wq_nonneg q n) (indicator_rpow_nonneg n t)))
  have hg2n : ∀ t, 0 ≤ g2 t := fun t => indicator_nonneg (fun t ht =>
    mul_nonneg hM (Real.rpow_nonneg (by have : (Y : ℝ) < t := ht; linarith) _)) t
  have hpt : ∀ t ∈ Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t ≤ g1 t + g2 t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    by_cases htY : t ≤ Y
    · exact (rpow_mul_rieszSumR_le hq Y ht0 htY).trans (le_add_of_nonneg_right (hg2n t))
    · push Not at htY
      have hg2t : g2 t = M * t ^ (θ - 2) := by rw [hg2, indicator_of_mem (show t ∈ Ioi (Y : ℝ) from htY)]
      have hp : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
      calc t ^ (-2 : ℝ) * rieszSumR (Tc q) t ≤ t ^ (-2 : ℝ) * |rieszSumR (Tc q) t| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hp
        _ ≤ t ^ (-2 : ℝ) * (M * t ^ θ) := mul_le_mul_of_nonneg_left (hT t htY) hp
        _ = M * t ^ (θ - 2) := by
            rw [mul_left_comm, ← Real.rpow_add ht0]; ring_nf
        _ ≤ g1 t + g2 t := by rw [hg2t]; exact le_add_of_nonneg_left (hg1n t)
  have hint1 : ∫ t in Ioi (0 : ℝ), g1 t =
      (q - 1) * ∑ n ∈ Finset.Ioc 0 Y, (if (n : ZMod q) = 1 then Λ n / n else 0) := by
    rw [hg1, integral_const_mul, integral_finsetSum _ (fun n hn =>
      (integrableOn_indicator_rpow n (Finset.mem_Ioc.mp hn).1).const_mul _)]
    congr 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [integral_const_mul, integral_indicator_rpow (Finset.mem_Ioc.mp hn).1]
    unfold wq
    split_ifs <;> simp [div_eq_mul_inv]
  have hint2 : ∫ t in Ioi (0 : ℝ), g2 t = M * (Y : ℝ) ^ (θ - 1) / (1 - θ) := by
    rw [hg2, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi hY0.le), integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hY0]
    have h3 : θ - 2 + 1 = θ - 1 := by ring
    rw [h3, neg_div, ← div_neg, neg_sub, mul_div_assoc]
  calc ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t
      ≤ ∫ t in Ioi (0 : ℝ), (g1 t + g2 t) :=
        setIntegral_mono_on hint (i1.add i2) measurableSet_Ioi hpt
    _ = _ := by rw [integral_add i1 i2, hint1, hint2]

/-- Lower bound for the Mellin integral of `Tc q`: the negative part of the Riesz sum is at most
`c x` up to `Y`. -/
theorem neg_integral_rieszSumR_le {q : ℕ} {Y : ℝ} (hY : 1 ≤ Y) {θ M c : ℝ} (hθ : θ < 1)
    (hc : 0 ≤ c) (hM : 0 ≤ M)
    (h1 : ∀ x : ℝ, 1 ≤ x → x ≤ Y → -rieszSumR (Tc q) x ≤ c * x)
    (h2 : ∀ x : ℝ, Y < x → |rieszSumR (Tc q) x| ≤ M * x ^ θ)
    (hint : IntegrableOn (fun t => t ^ (-2 : ℝ) * rieszSumR (Tc q) t) (Ioi 0)) :
    -∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t ≤
      c * Real.log Y + M * Y ^ (θ - 1) / (1 - θ) := by
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
  have hpt : ∀ t ∈ Ioi (0 : ℝ), -(t ^ (-2 : ℝ) * rieszSumR (Tc q) t) ≤ g1 t + g2 t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hi1 : 0 ≤ g1 t := indicator_nonneg (fun t ht =>
      mul_nonneg hc (inv_nonneg.mpr (by linarith [ht.1]))) t
    have hi2 : 0 ≤ g2 t := indicator_nonneg (fun t ht =>
      mul_nonneg hM (Real.rpow_nonneg (by have : Y < t := ht; linarith) _)) t
    have hp : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    by_cases ht1 : t < 1
    · rw [rieszSumR_eq_zero_of_lt_one _ ht1, mul_zero, neg_zero]
      exact add_nonneg hi1 hi2
    · push Not at ht1
      by_cases htY : t ≤ Y
      · have hm : t ∈ Icc 1 Y := ⟨ht1, htY⟩
        have hg1t : g1 t = c * t⁻¹ := by rw [hg1def, indicator_of_mem hm]
        rw [hg1t]
        calc -(t ^ (-2 : ℝ) * rieszSumR (Tc q) t) = t ^ (-2 : ℝ) * (-rieszSumR (Tc q) t) := by
              ring
          _ ≤ t ^ (-2 : ℝ) * (c * t) := mul_le_mul_of_nonneg_left (h1 t ht1 htY) hp
          _ = c * t⁻¹ := by
              rw [Real.rpow_neg ht0.le, Real.rpow_two]; field_simp
          _ ≤ c * t⁻¹ + g2 t := le_add_of_nonneg_right hi2
      · push Not at htY
        have hm : t ∈ Ioi Y := htY
        have hm' : t ∉ Icc 1 Y := fun h => by linarith [h.2]
        have hg1t : g1 t = 0 := by rw [hg1def, indicator_of_notMem hm']
        have hg2t : g2 t = M * t ^ (θ - 2) := by rw [hg2def, indicator_of_mem hm]
        rw [hg1t, hg2t, zero_add]
        calc -(t ^ (-2 : ℝ) * rieszSumR (Tc q) t) = t ^ (-2 : ℝ) * (-rieszSumR (Tc q) t) := by
              ring
          _ ≤ t ^ (-2 : ℝ) * |rieszSumR (Tc q) t| :=
              mul_le_mul_of_nonneg_left (neg_le_abs _) hp
          _ ≤ t ^ (-2 : ℝ) * (M * t ^ θ) := mul_le_mul_of_nonneg_left (h2 t htY) hp
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
  calc -∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t
      = ∫ t in Ioi (0 : ℝ), -(t ^ (-2 : ℝ) * rieszSumR (Tc q) t) := (integral_neg _).symm
    _ ≤ ∫ t in Ioi (0 : ℝ), (g1 t + g2 t) :=
        setIntegral_mono_on hint.neg (i1.add i2).integrableOn measurableSet_Ioi hpt
    _ = c * Real.log Y + M * Y ^ (θ - 1) / (1 - θ) := by
        rw [integral_add i1.restrict i2.restrict, hint1, hint2]

/-- The tail `M Y^{θ0 - 1}` with `M = q K log (q + 2)` and `Y = q^17` is at most `2K`. -/
lemma tail_le {q : ℕ} (hq : 1 ≤ q) {K : ℝ} (hK : 0 ≤ K) :
    (q * (K * Real.log (q + 2))) * ((q ^ 17 : ℕ) : ℝ) ^ (θ0 - 1) ≤ 2 * K := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hY : ((q ^ 17 : ℕ) : ℝ) ^ (θ0 - 1) ≤ ((q : ℝ) ^ 2)⁻¹ := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_two,
      ← Real.rpow_neg hq0.le]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    unfold θ0; norm_num
  have hlog : Real.log (q + 2) ≤ 2 * q := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q + 2 by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ (q : ℝ) * (K * Real.log (q + 2)) := by positivity
  calc (q * (K * Real.log (q + 2))) * ((q ^ 17 : ℕ) : ℝ) ^ (θ0 - 1)
      ≤ (q * (K * Real.log (q + 2))) * ((q : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hY hM0
    _ = K * Real.log (q + 2) / q := by field_simp
    _ ≤ 2 * K := by
        rw [div_le_iff₀ hq0]
        calc K * Real.log (q + 2) ≤ K * (2 * q) := mul_le_mul_of_nonneg_left hlog hK
          _ = 2 * K * q := by ring

/-- **Theorem (B).** Under the zero-free half-plane, for every prime `q ≥ 3` the sum of
`L'/L(1, χ)` over the nonprincipal characters modulo `q` is a real number `r` with
`-C log q log log q ≤ r ≤ C log q`. -/
theorem sum_logDeriv_one_of_zeroFree (hZ : Main.ZeroFree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], q.Prime → 3 ≤ q → ∃ r : ℝ,
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 = r ∧
        -(C * Real.log q * Real.log (Real.log q)) ≤ r ∧ r ≤ C * Real.log q := by
  obtain ⟨K, hK, hKb⟩ := riesz_bound_of_zeroFree hZ
  obtain ⟨C0, hC0, hS⟩ := sum_progression_bound
  have hθ : θ0 < 1 := by unfold θ0; norm_num
  have h1θ : 0 < 1 - θ0 := by linarith
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : 0 < c := by positivity
  set A : ℝ := 2 * K / (1 - θ0) with hA
  have hA0 : 0 < A := by positivity
  have hl3 : 1 < Real.log 3 := one_lt_log_three
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hl3
  refine ⟨2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3)) + 34 * c + 2 * A / Real.log 3,
    by positivity, ?_⟩
  intro q _ hq hq3
  have hq1 : 1 ≤ q := by omega
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  set lq : ℝ := Real.log q with hlq
  have hL3 : Real.log 3 ≤ lq := Real.log_le_log (by norm_num) hq3r
  have hL1 : 1 < lq := lt_of_lt_of_le hl3 hL3
  have hLL3 : Real.log (Real.log 3) ≤ Real.log lq := Real.log_le_log (by linarith) hL3
  have hLL0 : 0 < Real.log lq := lt_of_lt_of_le hll3 hLL3
  set K1 : ℝ := K * Real.log (q + 2) with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg hK.le (Real.log_nonneg (by linarith))
  have hKq : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K1 * x ^ θ0 := by
    intro χ hχ x hx
    have := hKb q χ hχ x hx
    calc ‖rieszSum (↗χ * ↗Λ) x‖ ≤ K * x ^ θ0 * Real.log (q + 2) := this
      _ = K1 * x ^ θ0 := by rw [hK1]; ring
  set M : ℝ := q * K1 with hM
  have hM0 : 0 ≤ M := mul_nonneg (Nat.cast_nonneg q) hK10
  have hT : ∀ t : ℝ, 1 ≤ t → |rieszSumR (Tc q) t| ≤ M * t ^ θ0 := fun t ht => by
    rw [hM]; exact abs_rieszSumR_Tc_le hq hK10 hKq ht
  have hint := integrableOn_rieszSumR_Tc hθ hT
  set I : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rieszSumR (Tc q) t with hI
  have hsum := sum_neg_logDeriv_eq hq hθ hKq
  set Y : ℕ := q ^ 17 with hYdef
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have hY1r : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hlogY : Real.log (Y : ℝ) = 17 * lq := by
    rw [hYdef, Nat.cast_pow, Real.log_pow]; push_cast; ring
  have htail : M * (Y : ℝ) ^ (θ0 - 1) / (1 - θ0) ≤ A := by
    rw [hA]
    apply div_le_div_of_nonneg_right _ h1θ.le
    exact tail_le hq1 hK.le
  -- upper bound for `I`
  have hup := integral_rieszSumR_le hq1 hY1 hθ hM0
    (fun t ht => hT t (le_trans hY1r ht.le)) hint
  have hSq := hS q hq hq3
  have hS1 : ((q : ℝ) - 1) * ∑ n ∈ Finset.Ioc 0 Y, (if (n : ZMod q) = 1 then Λ n / n else 0) ≤
      C0 * lq * Real.log lq := by
    have hq0 : (0 : ℝ) < q := by linarith
    have hB : 0 ≤ C0 * lq * Real.log lq / q := by positivity
    calc ((q : ℝ) - 1) * ∑ n ∈ Finset.Ioc 0 Y, (if (n : ZMod q) = 1 then Λ n / n else 0)
        ≤ ((q : ℝ) - 1) * (C0 * lq * Real.log lq / q) :=
          mul_le_mul_of_nonneg_left hSq (by linarith)
      _ ≤ q * (C0 * lq * Real.log lq / q) := mul_le_mul_of_nonneg_right (by linarith) hB
      _ = C0 * lq * Real.log lq := by field_simp
  have hIup : I ≤ C0 * lq * Real.log lq + A := by linarith
  -- lower bound for `I`
  have hlow := neg_integral_rieszSumR_le hY1r hθ hc0.le hM0
    (fun x hx _ => (neg_rieszSumR_le_psi hq1 (by linarith)).trans
      (Chebyshev.psi_le_const_mul_self (by linarith)))
    (fun x hx => hT x (le_trans hY1r hx.le)) hint
  rw [hlogY] at hlow
  have hIlow : -I ≤ 17 * c * lq + A := by linarith
  refine ⟨-2 * I, ?_, ?_, ?_⟩
  · have h : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
        -∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun χ _ => ?_)
      rw [neg_div, neg_neg]
    rw [h, hsum]
    push_cast
    ring
  · have hA1 : A ≤ A / (Real.log 3 * Real.log (Real.log 3)) * (lq * Real.log lq) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : Real.log 3 * Real.log (Real.log 3) ≤ lq * Real.log lq :=
        mul_le_mul hL3 hLL3 hll3.le (by linarith)
      nlinarith
    have hrest : 0 ≤ (34 * c + 2 * A / Real.log 3) * lq * Real.log lq := by positivity
    have key : 2 * (C0 * lq * Real.log lq + A) ≤
        (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3)) + 34 * c + 2 * A / Real.log 3) *
          lq * Real.log lq := by
      have e : (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3)) + 34 * c +
          2 * A / Real.log 3) * lq * Real.log lq =
          2 * (C0 * lq * Real.log lq) +
            2 * (A / (Real.log 3 * Real.log (Real.log 3)) * (lq * Real.log lq)) +
            (34 * c + 2 * A / Real.log 3) * lq * Real.log lq := by ring
      rw [e]
      linarith
    linarith
  · have hA1 : A ≤ A / Real.log 3 * lq := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have hrest : 0 ≤ (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3))) * lq := by
      positivity
    have key : 2 * (17 * c * lq + A) ≤
        (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3)) + 34 * c + 2 * A / Real.log 3) *
          lq := by
      have e : (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3)) + 34 * c +
          2 * A / Real.log 3) * lq =
          (2 * C0 + 2 * A / (Real.log 3 * Real.log (Real.log 3))) * lq + 2 * (17 * c * lq) +
            2 * (A / Real.log 3 * lq) := by ring
      rw [e]
      linarith
    linarith

end Vinogradov.EulerKronecker
