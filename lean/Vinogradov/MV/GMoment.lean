/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The fourth moment of `G(h) = ∏_{p ∣ h} p/(p-1)`: `∑_{h ≤ X} G(h)⁴ ≤ e³⁰ X`.
-/
import Vinogradov.MV.PairSieve
import Mathlib.Analysis.PSeries

noncomputable section

open Finset
open scoped Finset

namespace Vinogradov.MV

theorem G_factor_pow_le {p : ℕ} (hp : p.Prime) : ((p:ℝ) / (p - 1)) ^ 4 ≤ 1 + 30 / p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  set t : ℝ := (p:ℝ) - 1 with ht
  have ht1 : 1 ≤ t := by linarith
  have hp' : (p:ℝ) = t + 1 := by rw [ht]; ring
  rw [hp', div_pow, div_le_iff₀ (by positivity), add_div' _ _ _ (by linarith),
    div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) ht1 3, mul_le_mul_of_nonneg_left ht1
    (by positivity : (0:ℝ) ≤ t ^ 3), mul_le_mul_of_nonneg_left ht1 (by positivity : (0:ℝ) ≤ t ^ 2),
    mul_le_mul_of_nonneg_left ht1 (by positivity : (0:ℝ) ≤ t)]

theorem G_pow_four_le (h : ℕ) :
    G h ^ 4 ≤ ∑ S ∈ h.primeFactors.powerset, ∏ p ∈ S, (30 / (p:ℝ)) := by
  unfold G
  rw [← Finset.prod_pow, ← Finset.prod_one_add]
  apply Finset.prod_le_prod₀
  · intro p hp
    have h1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    apply pow_nonneg; apply div_nonneg <;> linarith
  · intro p hp
    exact G_factor_pow_le (Nat.prime_of_mem_primeFactors hp)

theorem card_filter_subset_primeFactors_le (X : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (#{h ∈ Icc 1 X | S ⊆ h.primeFactors} : ℝ) ≤ X / ∏ p ∈ S, (p:ℝ) := by
  have hsub : {h ∈ Icc 1 X | S ⊆ h.primeFactors} ⊆ {x ∈ Ioc 0 X | (∏ p ∈ S, p) ∣ x} := by
    intro h hh
    rw [mem_filter, mem_Icc] at hh
    rw [mem_filter, mem_Ioc]
    refine ⟨⟨by omega, hh.1.2⟩, ?_⟩
    apply Finset.prod_primes_dvd
    · intro a ha; exact (hS a ha).prime
    · intro a ha; exact Nat.dvd_of_mem_primeFactors (hh.2 ha)
  calc (#{h ∈ Icc 1 X | S ⊆ h.primeFactors} : ℝ)
      ≤ (#{x ∈ Ioc 0 X | (∏ p ∈ S, p) ∣ x} : ℝ) := by exact_mod_cast card_le_card hsub
    _ = ((X / ∏ p ∈ S, p : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ (X : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) := Nat.cast_div_le
    _ = _ := by push_cast; rfl

/-- `∑_{h ≤ X} G(h)⁴ ≤ e³⁰ X`. -/
theorem sum_G_pow_four_le (X : ℕ) : ∑ h ∈ Icc 1 X, G h ^ 4 ≤ Real.exp 30 * X := by
  set PS := (Icc 1 X).filter Nat.Prime
  have hpf : ∀ h ∈ Icc 1 X, h.primeFactors ⊆ PS := by
    intro h hh p hp
    rw [mem_Icc] at hh
    rw [mem_filter, mem_Icc]
    have := Nat.le_of_mem_primeFactors hp
    exact ⟨⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le, by omega⟩,
      Nat.prime_of_mem_primeFactors hp⟩
  have hpow : ∀ h ∈ Icc 1 X, h.primeFactors.powerset = PS.powerset.filter (· ⊆ h.primeFactors) := by
    intro h hh
    ext S
    simp only [mem_powerset, mem_filter]
    exact ⟨fun hS => ⟨hS.trans (hpf h hh), hS⟩, fun hS => hS.2⟩
  have hw : ∀ S ∈ PS.powerset, 0 ≤ ∏ p ∈ S, (30 / (p:ℝ)) := fun S _ =>
    Finset.prod_nonneg (fun p _ => by positivity)
  calc ∑ h ∈ Icc 1 X, G h ^ 4
      ≤ ∑ h ∈ Icc 1 X, ∑ S ∈ h.primeFactors.powerset, ∏ p ∈ S, (30 / (p:ℝ)) :=
        sum_le_sum (fun h _ => G_pow_four_le h)
    _ = ∑ h ∈ Icc 1 X, ∑ S ∈ PS.powerset,
          (if S ⊆ h.primeFactors then ∏ p ∈ S, (30 / (p:ℝ)) else 0) := by
        apply sum_congr rfl
        intro h hh
        rw [hpow h hh, sum_filter]
    _ = ∑ S ∈ PS.powerset, (∏ p ∈ S, (30 / (p:ℝ))) * #{h ∈ Icc 1 X | S ⊆ h.primeFactors} := by
        rw [sum_comm]
        apply sum_congr rfl
        intro S _
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ PS.powerset, (∏ p ∈ S, (30 / (p:ℝ))) * (X / ∏ p ∈ S, (p:ℝ)) := by
        apply sum_le_sum
        intro S hS
        apply mul_le_mul_of_nonneg_left _ (hw S hS)
        apply card_filter_subset_primeFactors_le
        intro p hp
        exact (mem_filter.mp (mem_powerset.mp hS hp)).2
    _ = X * ∑ S ∈ PS.powerset, ∏ p ∈ S, (30 / (p:ℝ) ^ 2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        rw [mul_div_assoc', mul_comm, mul_div_assoc, ← prod_div_distrib]
        congr 1
        apply prod_congr rfl
        intro p _
        ring
    _ = X * ∏ p ∈ PS, (1 + 30 / (p:ℝ) ^ 2) := by rw [prod_one_add]
    _ ≤ X * ∏ p ∈ PS, Real.exp (30 / (p:ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply prod_le_prod₀
        · intro p _; positivity
        · intro p _; rw [add_comm]; exact Real.add_one_le_exp _
    _ = X * Real.exp (30 * ∑ p ∈ PS, ((p:ℝ) ^ 2)⁻¹) := by
        rw [← Real.exp_sum, mul_sum]
        congr 2
    _ ≤ X * Real.exp 30 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [Real.exp_le_exp]
        have hsub : PS ⊆ Ioo 1 (X + 1) := by
          intro p hp
          rw [mem_filter, mem_Icc] at hp
          rw [mem_Ioo]
          exact ⟨hp.2.one_lt, by omega⟩
        have h1 : ∑ p ∈ PS, ((p:ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo 1 (X + 1), ((i:ℝ) ^ 2)⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        have h2 := sum_Ioo_inv_sq_le (α := ℝ) 1 (X + 1)
        norm_num at h2
        nlinarith
    _ = _ := by ring

end Vinogradov.MV
