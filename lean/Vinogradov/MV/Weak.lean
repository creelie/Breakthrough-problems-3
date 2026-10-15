/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The weak Montgomery–Vaughan bound: for completely multiplicative `f` with `‖f‖ ≤ 1`,
`|α - a/r| ≤ r⁻²` and `2 ≤ R ≤ r ≤ N/R`,
`‖∑_{n ≤ N} f(n) e(nα)‖ ≤ C (N / log N + N (log N)² / R^{1/4})`.
-/
import Vinogradov.MV.LargePrimes
import Vinogradov.MV.Reduction
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

open Finset Complex Vinogradov.PV
open scoped Finset

namespace Vinogradov.MV

theorem sum_half_pow_le (I : ℕ) : ∑ i ∈ range I, (1 / 2 : ℝ) ^ i ≤ 2 := by
  have key : ∀ I : ℕ, ∑ i ∈ range I, (1 / 2 : ℝ) ^ i = 2 - 2 * (1 / 2) ^ I := by
    intro I
    induction I with
    | zero => norm_num
    | succ I ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [key]
  have : 0 ≤ 2 * (1 / 2 : ℝ) ^ I := by positivity
  linarith

theorem sum_two_pow_le (I : ℕ) : ∑ i ∈ range I, (2 : ℝ) ^ i ≤ 2 ^ I := by
  induction I with
  | zero => norm_num
  | succ I ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem sum_four_pow_le (I : ℕ) : ∑ i ∈ range I, (4 : ℝ) ^ i ≤ 4 ^ I := by
  induction I with
  | zero => norm_num
  | succ I ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (0 : ℝ) ≤ 4 ^ I := by positivity
    linarith

/-- The 16-adic decomposition of `(0, 16^I - 1]`. -/
theorem sum_Ioc_sixteen (g : ℕ → ℂ) (I : ℕ) :
    ∑ m ∈ Ioc 0 (16 ^ I - 1), g m =
      ∑ i ∈ range I, ∑ m ∈ Ioc (16 ^ i - 1) (16 ^ i - 1 + 15 * 16 ^ i), g m := by
  induction I with
  | zero => simp
  | succ I ih =>
    have h1 : 1 ≤ 16 ^ I := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 16 ^ (I + 1) - 1 = 16 ^ I - 1 + 15 * 16 ^ I := by rw [pow_succ]; omega
    rw [Finset.sum_range_succ, ← ih, h2, sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)]

/-- **The large primes** `2^J < p ≤ N`, for `N < 2^J 16^I`. -/
theorem large_primes (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} {a : ℚ}
    (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (N J I : ℕ) (hJ : 1 ≤ J)
    (hN : N < 2 ^ J * 16 ^ I) {R : ℝ} (hR : 0 < R) (hRr : R ≤ a.den)
    (hrN : (a.den : ℝ) ≤ N / R) :
    ‖∑ p ∈ Ioc (2 ^ J) N with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤
      Kb * (2 * N + I * (N / q4 R) + 2 ^ I * q4 N ^ 3 +
        4 ^ I * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ))) := by
  have hP : 2 ≤ 2 ^ J := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
  set F : ℕ → ℕ → ℂ := fun p m => if p * m ≤ N then f m * e (p * m * α) else 0 with hF
  have hinner : ∀ p ∈ (Ioc (2 ^ J) N).filter Nat.Prime,
      ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α) =
        ∑ i ∈ range I, ∑ m ∈ Ioc (16 ^ i - 1) (16 ^ i - 1 + 15 * 16 ^ i), F p m := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have hp0 : 0 < p := by omega
    have hdiv : N / p ≤ 16 ^ I - 1 := by
      have : N / p < 16 ^ I := by
        rw [Nat.div_lt_iff_lt_mul hp0]
        calc N < 2 ^ J * 16 ^ I := hN
          _ ≤ p * 16 ^ I := Nat.mul_le_mul_right _ hp.1.1.le
          _ = 16 ^ I * p := mul_comm _ _
      omega
    rw [sum_Ioc_div_eq N p (16 ^ I - 1) hp0 hdiv, sum_Ioc_sixteen]
  rw [sum_congr rfl fun p hp => by rw [hinner p hp]]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine (norm_sum_le _ _).trans ?_
  have hblock : ∀ i ∈ range I, ‖∑ p ∈ Ioc (2 ^ J) N with p.Prime,
      ∑ m ∈ Ioc (16 ^ i - 1) (16 ^ i - 1 + 15 * 16 ^ i), (Real.log p : ℂ) * f p * F p m‖ ≤
      Kb * (N / 2 ^ i + N / q4 R + 2 ^ i * q4 N ^ 3 +
        4 ^ i * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ))) := by
    intro i _
    have hb := block_bound f hfb hα hr N (2 ^ J) i hP hR hRr hrN
    simp_rw [mul_sum] at hb
    exact hb
  refine (sum_le_sum hblock).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ Kb_pos.le
  simp only [sum_add_distrib]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq4n := q4_nonneg (N : ℝ)
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have g1 : ∑ i ∈ range I, (N : ℝ) / 2 ^ i ≤ 2 * N := by
    have : ∑ i ∈ range I, (N : ℝ) / 2 ^ i = N * ∑ i ∈ range I, (1 / 2 : ℝ) ^ i := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; rw [one_div_pow]; ring
    rw [this]
    nlinarith [sum_half_pow_le I]
  have g2 : ∑ i ∈ range I, (N : ℝ) / q4 R = I * (N / q4 R) := by
    rw [sum_const, card_range, nsmul_eq_mul]
  have g3 : ∑ i ∈ range I, (2 : ℝ) ^ i * q4 N ^ 3 ≤ 2 ^ I * q4 N ^ 3 := by
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_two_pow_le I) (by positivity)
  have g4 : ∑ i ∈ range I, (4 : ℝ) ^ i * Real.log ((N : ℝ) + 1) *
      Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ)) ≤
      4 ^ I * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ)) := by
    rw [← sum_mul, ← sum_mul]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (sum_four_pow_le I) hlog
  linarith

theorem eight_mul_le_two_pow {k : ℕ} (hk : 6 ≤ k) : 8 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 8 ≤ 2 ^ k := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega

/-- The parameters: `ℓ = ⌊log₂ N⌋ ≥ 64`, `I = ⌊log₂ ℓ⌋ + 1`, `J = ℓ + 1 - 4I`. -/
theorem params {N : ℕ} (hℓ : 64 ≤ Nat.log 2 N) : ∃ I J : ℕ, 1 ≤ J ∧ N < 2 ^ J * 16 ^ I ∧
    2 ^ J ≤ N ∧ J ^ 2 * 2 ^ J ≤ 2 * N ∧ 4 * I ≤ Nat.log 2 N ∧ J ≤ Nat.log 2 N ∧
    2 ^ I ≤ 2 * Nat.log 2 N := by
  have hN0 : N ≠ 0 := by
    rintro rfl; simp at hℓ
  have hℓ0 : Nat.log 2 N ≠ 0 := by omega
  have hlog6 : 6 ≤ Nat.log 2 (Nat.log 2 N) :=
    Nat.le_log_of_pow_le (by norm_num) (by
      calc 2 ^ 6 = 64 := by norm_num
        _ ≤ Nat.log 2 N := hℓ)
  have hlt : Nat.log 2 N < 2 ^ (Nat.log 2 (Nat.log 2 N) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : 2 ^ (Nat.log 2 (Nat.log 2 N) + 1) ≤ 2 * Nat.log 2 N := by
    rw [pow_succ]; have := Nat.pow_log_le_self 2 hℓ0; omega
  have h8 : 8 * (Nat.log 2 (Nat.log 2 N) + 1) ≤ 2 ^ (Nat.log 2 (Nat.log 2 N) + 1) :=
    eight_mul_le_two_pow (by omega)
  have hNlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNge : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  set ℓ := Nat.log 2 N with hℓdef
  set I := Nat.log 2 ℓ + 1 with hIdef
  have h4I : 4 * I ≤ ℓ := by omega
  refine ⟨I, ℓ + 1 - 4 * I, by omega, ?_, ?_, ?_, h4I, by omega, hle⟩
  · have : 2 ^ (ℓ + 1 - 4 * I) * 16 ^ I = 2 ^ (ℓ + 1) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
      congr 1; omega
    rw [this]; exact hNlt
  · calc 2 ^ (ℓ + 1 - 4 * I) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ N := hNge
  · have hJ : ℓ + 1 - 4 * I < 2 ^ I := by omega
    have hJ2 : (ℓ + 1 - 4 * I) ^ 2 ≤ 16 ^ I := by
      calc (ℓ + 1 - 4 * I) ^ 2 ≤ (2 ^ I) ^ 2 := Nat.pow_le_pow_left hJ.le 2
        _ ≤ (2 ^ I) ^ 4 := Nat.pow_le_pow_right (by positivity) (by norm_num)
        _ = 16 ^ I := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h16 : 2 ^ (ℓ + 1 - 4 * I) * 16 ^ I = 2 * 2 ^ ℓ := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add,
        show ℓ + 1 - 4 * I + 4 * I = ℓ + 1 by omega, pow_succ, Nat.mul_comm (2 ^ ℓ)]
    calc (ℓ + 1 - 4 * I) ^ 2 * 2 ^ (ℓ + 1 - 4 * I) ≤ 16 ^ I * 2 ^ (ℓ + 1 - 4 * I) :=
          Nat.mul_le_mul_right _ hJ2
      _ = 2 * 2 ^ ℓ := by rw [Nat.mul_comm (16 ^ I)]; exact h16
      _ ≤ 2 * N := by omega

/-- `(log x)⁶ (2x)^{3/5} ≤ 2 · 15⁶ x` for `x ≥ 1`. -/
theorem log_six_rpow_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 6 * (2 * x) ^ (3 / 5 : ℝ) ≤ 2 * 15 ^ 6 * x := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ 15 * x ^ (1 / 15 : ℝ) := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 15 by norm_num)
    calc Real.log x ≤ x ^ (1 / 15 : ℝ) / (1 / 15) := this
      _ = 15 * x ^ (1 / 15 : ℝ) := by ring
  have h6 : Real.log x ^ 6 ≤ 15 ^ 6 * x ^ (2 / 5 : ℝ) := by
    calc Real.log x ^ 6 ≤ (15 * x ^ (1 / 15 : ℝ)) ^ 6 := pow_le_pow_left₀ hl0 hl 6
      _ = 15 ^ 6 * (x ^ (1 / 15 : ℝ)) ^ (6 : ℕ) := by ring
      _ = 15 ^ 6 * x ^ (2 / 5 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1 / 15 : ℝ)) 6, ← Real.rpow_mul hx0.le]; norm_num
  have h2 : (2 * x) ^ (3 / 5 : ℝ) ≤ 2 * x ^ (3 / 5 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hadd : x ^ (2 / 5 : ℝ) * x ^ (3 / 5 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  calc Real.log x ^ 6 * (2 * x) ^ (3 / 5 : ℝ)
      ≤ 15 ^ 6 * x ^ (2 / 5 : ℝ) * (2 * x ^ (3 / 5 : ℝ)) :=
        mul_le_mul h6 h2 (by positivity) (by positivity)
    _ = 2 * 15 ^ 6 * (x ^ (2 / 5 : ℝ) * x ^ (3 / 5 : ℝ)) := by ring
    _ = 2 * 15 ^ 6 * x := by rw [hadd]

/-- `(log x)³ √(x (2x)^{3/5}) ≤ 2 · 15³ x` for `x ≥ 1`. -/
theorem log_cube_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 3 * Real.sqrt (x * (2 * x) ^ (3 / 5 : ℝ)) ≤ 2 * 15 ^ 3 * x := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hk := log_six_rpow_le hx
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc (Real.log x ^ 3) ^ 2 * (x * (2 * x) ^ (3 / 5 : ℝ))
      = x * (Real.log x ^ 6 * (2 * x) ^ (3 / 5 : ℝ)) := by ring
    _ ≤ x * (2 * 15 ^ 6 * x) := mul_le_mul_of_nonneg_left hk hx0.le
    _ = 2 * 15 ^ 6 * x ^ 2 := by ring
    _ ≤ 4 * 15 ^ 6 * x ^ 2 := by linarith
    _ = (2 * 15 ^ 3 * x) ^ 2 := by ring

theorem norm_sum_le_N (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Ioc 0 N, ‖f n * e (n * α)‖ ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) :=
        sum_le_sum fun n _ => by rw [norm_mul, norm_e, mul_one]; exact hfb n
    _ = N := by simp

theorem sum_primes_split (g : ℕ → ℂ) {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ p ∈ Ioc 0 N with p.Prime, g p =
      ∑ p ∈ Ioc 1 M with p.Prime, g p + ∑ p ∈ Ioc M N with p.Prime, g p := by
  simp only [sum_filter]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le M) hMN,
    ← sum_Ioc_consecutive _ (by norm_num : (0 : ℕ) ≤ 1) hM]
  have h1 : ∑ p ∈ Ioc 0 1, (if p.Prime then g p else 0) = 0 := by
    rw [show Ioc 0 1 = ({1} : Finset ℕ) by ext x; simp only [mem_Ioc, mem_singleton]; omega]
    simp [Nat.not_prime_one]
  rw [h1, zero_add]

theorem norm_mul_log_le {S T1 T2 : ℂ} {L B : ℝ} (hL : 0 ≤ L)
    (h : ‖S * (L : ℂ) - (T1 + T2)‖ ≤ B) : ‖S‖ * L ≤ B + ‖T1‖ + ‖T2‖ := by
  have e1 : ‖S * (L : ℂ)‖ = ‖S‖ * L := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL]
  have h1 := norm_sub_norm_le (S * (L : ℂ)) (T1 + T2)
  have h2 := norm_add_le T1 T2
  linarith

/-- **The Montgomery–Vaughan bound, weak form.** For completely multiplicative `f` with
`‖f‖ ≤ 1`, `|α - a/r| ≤ r⁻²` and `2 ≤ R ≤ r ≤ N/R`,
`‖∑_{n ≤ N} f(n) e(nα)‖ ≤ C (N / log N + N (log N)² / R^{1/4})`. -/
theorem weak_mv : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ m n, f (m * n) = f m * f n) →
    (∀ n, ‖f n‖ ≤ 1) → ∀ (α : ℝ) (a : ℚ) (N : ℕ) (R : ℝ), 2 ≤ R → R ≤ a.den →
      (a.den : ℝ) ≤ N / R → |α - a| ≤ 1 / (a.den : ℝ) ^ 2 →
        ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ ≤
          C * (N / Real.log N + N * Real.log N ^ 2 / q4 R) := by
  obtain ⟨C0, hC0, hred⟩ := reduction
  have hKb := Kb_pos
  refine ⟨45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb), by positivity, ?_⟩
  intro f hfm hfb α a N R hR hRr hrN hα
  have hR0 : 0 < R := by linarith
  have hr0 : (0 : ℝ) < a.den := by exact_mod_cast a.den_pos
  have hr2 : 2 ≤ a.den := by
    have : (2 : ℝ) ≤ a.den := hR.trans hRr
    exact_mod_cast this
  have hrR : (a.den : ℝ) * R ≤ N := by rwa [le_div_iff₀ hR0] at hrN
  have hn4 : (4 : ℝ) ≤ N := by nlinarith
  have hN4 : 4 ≤ N := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < Real.log N := by linarith
  have hq4R1 : 1 ≤ q4 R := one_le_q4 (by linarith)
  have hq4R0 : 0 < q4 R := by linarith
  have hP1 : 0 ≤ (N : ℝ) / Real.log N := by positivity
  have hP2 : 0 ≤ (N : ℝ) * Real.log N ^ 2 / q4 R := by positivity
  by_cases hsmall : Nat.log 2 N < 64
  · -- small `N`: the trivial bound
    have hNlt : N < 2 ^ 64 :=
      calc N < 2 ^ (Nat.log 2 N).succ := Nat.lt_pow_succ_log_self (by norm_num) N
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hsmall
    have hL45 : Real.log N ≤ 45 := by
      have h1 : (N : ℝ) ≤ (2 : ℝ) ^ 64 := by exact_mod_cast hNlt.le
      have h2 : Real.log N ≤ Real.log ((2 : ℝ) ^ 64) := Real.log_le_log hn0 h1
      rw [Real.log_pow] at h2
      have := Real.log_two_lt_d9
      push_cast at h2
      linarith
    have hSN := norm_sum_le_N f hfb α N
    have h45 : ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ ≤ 45 * ((N : ℝ) / Real.log N) := by
      rw [mul_div_assoc', le_div_iff₀ hL0]
      have := mul_le_mul hSN hL45 hL0.le hn0.le
      linarith
    calc ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ ≤ 45 * ((N : ℝ) / Real.log N) := h45
      _ ≤ (45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb)) * ((N : ℝ) / Real.log N) := by
          apply mul_le_mul_of_nonneg_right _ hP1; linarith
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  · push Not at hsmall
    obtain ⟨I, J, hJ1, hNJ, hJN, hJ2, hIℓ, hJℓ, h2I⟩ := params hsmall
    have hM1 : 1 ≤ 2 ^ J := Nat.one_le_two_pow
    have hredN := hred f hfm hfb α N
    rw [sum_primes_split _ hM1 hJN] at hredN
    have hSL := norm_mul_log_le hL0.le hredN
    have hT1 := small_primes f hfb hα hr2 N J
    have hT2 := large_primes f hfb hα hr2 N J I hJ1 hNJ hR0 hRr hrN
    -- real forms of the parameter facts
    have hℓL : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
      have h1 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      have h2 : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      have h3 := Real.log_two_gt_d9
      have h4 : ((Nat.log 2 N : ℕ) : ℝ) * (1 / 2) ≤ (Nat.log 2 N : ℕ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      linarith
    have hJr : (J : ℝ) ≤ 2 * Real.log N := by
      have : (J : ℝ) ≤ (Nat.log 2 N : ℕ) := by exact_mod_cast hJℓ
      linarith
    have hJ1r : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
    have hIr : (I : ℝ) ≤ 2 * Real.log N := by
      have : (I : ℝ) ≤ (Nat.log 2 N : ℕ) := by exact_mod_cast (by omega : I ≤ Nat.log 2 N)
      linarith
    have h2Ir : (2 : ℝ) ^ I ≤ 4 * Real.log N := by
      have : ((2 ^ I : ℕ) : ℝ) ≤ ((2 * Nat.log 2 N : ℕ) : ℝ) := by exact_mod_cast h2I
      push_cast at this
      linarith
    have hJ2r : (J : ℝ) ^ 2 * 2 ^ J ≤ 2 * N := by exact_mod_cast hJ2
    have hL3 : Real.log N ≤ Real.log N ^ 3 := by
      have : Real.log N ^ 1 ≤ Real.log N ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
      simpa using this
    have hL23 : Real.log N ^ 2 ≤ Real.log N ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    have hQ2 : q4 R ^ 2 = Real.sqrt R := by
      unfold q4; exact Real.sq_sqrt (Real.sqrt_nonneg R)
    have hsR0 : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
    have hsR : Real.sqrt R ≤ R := sqrt_le_of_le_sq hR0.le (by nlinarith)
    have hX : 0 ≤ Real.log N ^ 3 * N / q4 R := by positivity
    -- the small primes
    have a1 : 3 * Real.sqrt 7 * (J : ℝ) * Real.sqrt ((N : ℝ) * 2 ^ J) ≤ 12 * N := by
      apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
      have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
      have hs : Real.sqrt ((N : ℝ) * 2 ^ J) ^ 2 = N * 2 ^ J := Real.sq_sqrt (by positivity)
      have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
      calc (3 * Real.sqrt 7 * (J : ℝ) * Real.sqrt ((N : ℝ) * 2 ^ J)) ^ 2
          = 63 * (N : ℝ) * ((J : ℝ) ^ 2 * 2 ^ J) := by rw [mul_pow, mul_pow, mul_pow, h7, hs]; ring
        _ ≤ 63 * (N : ℝ) * (2 * N) := mul_le_mul_of_nonneg_left hJ2r (by positivity)
        _ = 126 * (N : ℝ) ^ 2 := by ring
        _ ≤ 144 * (N : ℝ) ^ 2 := by linarith
        _ = (12 * (N : ℝ)) ^ 2 := by ring
    have hJsq : (J : ℝ) ^ 2 ≤ 4 * Real.log N ^ 3 := by
      have h1 : (J : ℝ) ^ 2 ≤ (2 * Real.log N) ^ 2 := pow_le_pow_left₀ (by positivity) hJr 2
      have h2 : (2 * Real.log N) ^ 2 = 4 * Real.log N ^ 2 := by ring
      linarith
    have hJcube : (J : ℝ) ^ 3 ≤ 8 * Real.log N ^ 3 := by
      have h1 : (J : ℝ) ^ 3 ≤ (2 * Real.log N) ^ 3 := pow_le_pow_left₀ (by positivity) hJr 3
      have h2 : (2 * Real.log N) ^ 3 = 8 * Real.log N ^ 3 := by ring
      linarith
    have hsq : Real.sqrt (24 / a.den) ≤ 5 / q4 R := by
      apply sqrt_le_of_le_sq (by positivity)
      rw [div_pow, hQ2, div_le_div_iff₀ hr0 hsR0]
      nlinarith
    have a2 : (J : ℝ) ^ 2 * N * Real.sqrt (24 / a.den) ≤ 20 * (Real.log N ^ 3 * N / q4 R) := by
      calc (J : ℝ) ^ 2 * N * Real.sqrt (24 / a.den)
          ≤ (4 * Real.log N ^ 3) * N * (5 / q4 R) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hJsq hn0.le) hsq (Real.sqrt_nonneg _)
              (by positivity)
        _ = 20 * (Real.log N ^ 3 * N / q4 R) := by ring
    have hsq3 : Real.sqrt (24 * J * N * a.den) ≤ 5 * J * N / q4 R := by
      apply sqrt_le_of_le_sq (by positivity)
      rw [div_pow, hQ2, le_div_iff₀ hsR0]
      have h1 : (a.den : ℝ) * Real.sqrt R ≤ N :=
        le_trans (mul_le_mul_of_nonneg_left hsR hr0.le) hrR
      have h2 : (J : ℝ) * (N : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ hJ1r two_ne_zero) (sq_nonneg _)
      have h3 : (0 : ℝ) ≤ (J : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
      calc 24 * (J : ℝ) * N * a.den * Real.sqrt R = 24 * ((J : ℝ) * N) * (a.den * Real.sqrt R) := by ring
        _ ≤ 24 * ((J : ℝ) * N) * N := by apply mul_le_mul_of_nonneg_left h1; positivity
        _ = 24 * ((J : ℝ) * (N : ℝ) ^ 2) := by ring
        _ ≤ 25 * ((J : ℝ) ^ 2 * (N : ℝ) ^ 2) := by linarith only [h2, h3]
        _ = (5 * (J : ℝ) * N) ^ 2 := by ring
    have a3 : (J : ℝ) ^ 2 * Real.sqrt (24 * J * N * a.den) ≤
        40 * (Real.log N ^ 3 * N / q4 R) := by
      calc (J : ℝ) ^ 2 * Real.sqrt (24 * J * N * a.den) ≤ (J : ℝ) ^ 2 * (5 * J * N / q4 R) :=
            mul_le_mul_of_nonneg_left hsq3 (by positivity)
        _ = 5 * ((J : ℝ) ^ 3 * N / q4 R) := by ring
        _ ≤ 5 * (8 * Real.log N ^ 3 * N / q4 R) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply div_le_div_of_nonneg_right _ hq4R0.le
            exact mul_le_mul_of_nonneg_right hJcube hn0.le
        _ = 40 * (Real.log N ^ 3 * N / q4 R) := by ring
    -- the large primes
    have b2 : (I : ℝ) * ((N : ℝ) / q4 R) ≤ 2 * (Real.log N ^ 3 * N / q4 R) := by
      calc (I : ℝ) * ((N : ℝ) / q4 R) ≤ (2 * Real.log N ^ 3) * ((N : ℝ) / q4 R) :=
            mul_le_mul_of_nonneg_right (by linarith only [hIr, hL3]) (by positivity)
        _ = 2 * (Real.log N ^ 3 * N / q4 R) := by ring
    have b3 : (2 : ℝ) ^ I * q4 N ^ 3 ≤ 16 * N := by
      have hq := log_le_four_q4 (Nat.cast_nonneg N)
      have hq0 := q4_nonneg (N : ℝ)
      have h1 : (2 : ℝ) ^ I ≤ 16 * q4 N := by linarith only [h2Ir, hq]
      calc (2 : ℝ) ^ I * q4 N ^ 3 ≤ 16 * q4 N * q4 N ^ 3 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 16 * q4 N ^ 4 := by ring
        _ = 16 * N := by rw [q4_pow_four (Nat.cast_nonneg N)]
    have b4 : (4 : ℝ) ^ I * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ)) ≤
        216000 * N := by
      have h4eq : (4 : ℝ) ^ I = ((2 : ℝ) ^ I) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h4I : (4 : ℝ) ^ I ≤ 16 * Real.log N ^ 2 := by
        rw [h4eq]
        calc ((2 : ℝ) ^ I) ^ 2 ≤ (4 * Real.log N) ^ 2 := pow_le_pow_left₀ (by positivity) h2Ir 2
          _ = 16 * Real.log N ^ 2 := by ring
      have hlogN1 : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log N := by
        have h1 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by nlinarith only [hn4]
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_pow] at h2
        push_cast at h2
        linarith only [h2]
      have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith only [hn0])
      have hprod : (4 : ℝ) ^ I * Real.log ((N : ℝ) + 1) ≤ 32 * Real.log N ^ 3 := by
        calc (4 : ℝ) ^ I * Real.log ((N : ℝ) + 1) ≤ (16 * Real.log N ^ 2) * (2 * Real.log N) :=
              mul_le_mul h4I hlogN1 hlog0 (by positivity)
          _ = 32 * Real.log N ^ 3 := by ring
      have hc := log_cube_sqrt_le (x := (N : ℝ)) (by linarith only [hn4])
      calc (4 : ℝ) ^ I * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ))
          ≤ 32 * Real.log N ^ 3 * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg _)
        _ = 32 * (Real.log N ^ 3 * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ))) := by ring
        _ ≤ 32 * (2 * 15 ^ 3 * N) := mul_le_mul_of_nonneg_left hc (by norm_num)
        _ = 216000 * N := by ring
    have hT2' : ‖∑ p ∈ Ioc (2 ^ J) N with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤
        Kb * (216018 * N + 2 * (Real.log N ^ 3 * N / q4 R)) := by
      refine hT2.trans (mul_le_mul_of_nonneg_left ?_ hKb.le)
      linarith only [b2, b3, b4]
    -- assembly
    have hA : ‖∑ n ∈ Ioc 0 N, f n * e (n * α)‖ * Real.log N ≤
        (C0 + 908 + 216018 * Kb) * N + (60 + 2 * Kb) * (Real.log N ^ 3 * N / q4 R) := by
      linarith only [hSL, hT1, a1, a2, a3, hT2']
    have hC1 : C0 + 908 + 216018 * Kb ≤ 45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb) := by
      linarith only [hKb]
    have hC2 : 60 + 2 * Kb ≤ 45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb) := by
      linarith only [hKb, hC0]
    have e1 : (45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb)) *
        ((N : ℝ) / Real.log N + N * Real.log N ^ 2 / q4 R) * Real.log N =
        (45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb)) * N +
          (45 + C0 + 908 + 216018 * Kb + (60 + 2 * Kb)) * (Real.log N ^ 3 * N / q4 R) := by
      field_simp
    apply le_of_mul_le_mul_right _ hL0
    rw [e1]
    have k1 := mul_le_mul_of_nonneg_right hC1 hn0.le
    have k2 := mul_le_mul_of_nonneg_right hC2 hX
    linarith only [hA, k1, k2]

end Vinogradov.MV
