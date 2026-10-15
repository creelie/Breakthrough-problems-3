/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The sum of `Λ(n)/n` over `n ≡ 1 mod q`, `n ≤ q^17`, is `≪ log q log log q / q`.
-/
import Mathlib
import Vinogradov.EulerKronecker.BlockSieve

noncomputable section

open scoped Nat ArithmeticFunction.vonMangoldt
open scoped Finset

namespace Vinogradov.EulerKronecker

/-- `(j + 1)^4 2^{j/32} ≤ (48 / c^4) 2^j` with `c = (31/32) log 2`. -/
lemma pow_four_mul_rpow_le (j : ℕ) :
    ((j:ℝ) + 1) ^ 4 * (2:ℝ) ^ ((j:ℝ) / 32) ≤ 48 / (31 / 32 * Real.log 2) ^ 4 * 2 ^ j := by
  set c : ℝ := 31 / 32 * Real.log 2 with hc
  have hc0 : 0 < c := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hx : 0 ≤ c * ((j:ℝ) + 1) := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx 4
  have hfact : ((4 : ℕ)! : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact] at h1
  have h1' : (c * ((j:ℝ) + 1)) ^ 4 ≤ 24 * Real.exp (c * ((j:ℝ) + 1)) := by
    rw [div_le_iff₀ (by norm_num)] at h1; linarith
  have hexp : Real.exp (c * ((j:ℝ) + 1)) = (2:ℝ) ^ (31 / 32 * ((j:ℝ) + 1)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), hc]; congr 1; ring
  have h2 : ((j:ℝ) + 1) ^ 4 ≤ 24 / c ^ 4 * (2:ℝ) ^ (31 / 32 * ((j:ℝ) + 1)) := by
    have e : ((j:ℝ) + 1) ^ 4 = (c * ((j:ℝ) + 1)) ^ 4 / c ^ 4 := by field_simp
    rw [e, ← hexp, div_le_iff₀ (by positivity)]
    have : 24 / c ^ 4 * Real.exp (c * ((j:ℝ) + 1)) * c ^ 4 =
        24 * Real.exp (c * ((j:ℝ) + 1)) := by field_simp
    rw [this]; exact h1'
  have h3 : (2:ℝ) ^ (31 / 32 * ((j:ℝ) + 1)) * (2:ℝ) ^ ((j:ℝ) / 32) ≤ 2 * 2 ^ j := by
    rw [← Real.rpow_add (by norm_num)]
    have : 31 / 32 * ((j:ℝ) + 1) + (j:ℝ) / 32 = (j:ℝ) + 31 / 32 := by ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_natCast, mul_comm]
    gcongr
    calc (2:ℝ) ^ (31 / 32 : ℝ) ≤ 2 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc ((j:ℝ) + 1) ^ 4 * (2:ℝ) ^ ((j:ℝ) / 32)
      ≤ 24 / c ^ 4 * (2:ℝ) ^ (31 / 32 * ((j:ℝ) + 1)) * (2:ℝ) ^ ((j:ℝ) / 32) := by gcongr
    _ = 24 / c ^ 4 * ((2:ℝ) ^ (31 / 32 * ((j:ℝ) + 1)) * (2:ℝ) ^ ((j:ℝ) / 32)) := by ring
    _ ≤ 24 / c ^ 4 * (2 * 2 ^ j) := by gcongr
    _ = 48 / c ^ 4 * 2 ^ j := by ring

/-- **Brun–Titchmarsh on dyadic blocks.** At most `C₁ 2^j / (j + 1)` of the numbers
`1 + (2^j + m) q`, `m < 2^j`, are prime powers, when `2^{j/32} < q`. -/
theorem block_count_le : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (q : ℕ), q.Prime → ∀ j : ℕ,
    (2:ℝ) ^ ((j:ℝ) / 32) < q →
    (#{m ∈ Finset.range (2 ^ j) | IsPrimePow (apTerm q (2 ^ j) m)} : ℝ) ≤
      C₁ * 2 ^ j / ((j:ℝ) + 1) := by
  set c : ℝ := 31 / 32 * Real.log 2 with hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by positivity
  refine ⟨32 + 128 / Real.log 2 + 2 * (48 / c ^ 4), by positivity, ?_⟩
  intro q hq j hjq
  have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have htriv : (#{m ∈ Finset.range (2 ^ j) | IsPrimePow (apTerm q (2 ^ j) m)} : ℝ) ≤ 2 ^ j := by
    have := Finset.card_filter_le (Finset.range (2 ^ j)) (fun m => IsPrimePow (apTerm q (2 ^ j) m))
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hrest : 0 ≤ 128 / Real.log 2 + 2 * (48 / c ^ 4) := by positivity
  by_cases hj : j < 32
  · calc _ ≤ (2:ℝ) ^ j := htriv
      _ ≤ 32 * 2 ^ j / ((j:ℝ) + 1) := by
          rw [le_div_iff₀ hj1]
          have : (j:ℝ) + 1 ≤ 32 := by exact_mod_cast (by omega : j + 1 ≤ 32)
          nlinarith
      _ ≤ _ := by gcongr; linarith
  · push Not at hj
    have hj32 : (32:ℝ) ≤ j := by exact_mod_cast hj
    set z : ℝ := (2:ℝ) ^ ((j:ℝ) / 32) with hz
    have hz1 : 1 < z := Real.one_lt_rpow (by norm_num) (by positivity)
    have hz0 : 0 < z := by positivity
    have hlogz : Real.log z = (j:ℝ) / 32 * Real.log 2 := Real.log_rpow (by norm_num) _
    have hB := card_primePow_le hq (2 ^ j) hz1 hjq
    push_cast at hB
    have e1 : 2 * (2:ℝ) ^ j / Real.log z ≤ 128 / Real.log 2 * 2 ^ j / ((j:ℝ) + 1) := by
      rw [hlogz, div_le_div_iff₀ (by positivity) hj1]
      have : 128 / Real.log 2 * 2 ^ j * ((j:ℝ) / 32 * Real.log 2) = 4 * 2 ^ j * j := by
        field_simp; ring
      rw [this]; nlinarith
    have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have hlz : Real.log z ≤ j := by
      rw [hlogz]
      have : (j:ℝ) / 32 * Real.log 2 ≤ (j:ℝ) / 32 * 1 := by gcongr
      linarith
    have hlz0 : 0 ≤ Real.log z := (Real.log_pos hz1).le
    have e2 : z * (1 + Real.log z) ^ 3 + z ≤ 2 * (48 / c ^ 4) * 2 ^ j / ((j:ℝ) + 1) := by
      calc z * (1 + Real.log z) ^ 3 + z ≤ 2 * z * ((j:ℝ) + 1) ^ 3 := by
            have h1 : (1 + Real.log z) ^ 3 ≤ ((j:ℝ) + 1) ^ 3 :=
              pow_le_pow_left₀ (by linarith) (by linarith) 3
            have h2 : 1 ≤ ((j:ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
            nlinarith
        _ = 2 * (((j:ℝ) + 1) ^ 4 * z) / ((j:ℝ) + 1) := by field_simp
        _ ≤ 2 * (48 / c ^ 4 * 2 ^ j) / ((j:ℝ) + 1) := by
            apply div_le_div_of_nonneg_right _ hj1.le
            exact mul_le_mul_of_nonneg_left (pow_four_mul_rpow_le j) (by norm_num)
        _ = _ := by ring
    calc _ ≤ 2 * (2:ℝ) ^ j / Real.log z + z * (1 + Real.log z) ^ 3 + z := hB
      _ ≤ 128 / Real.log 2 * 2 ^ j / ((j:ℝ) + 1) + 2 * (48 / c ^ 4) * 2 ^ j / ((j:ℝ) + 1) := by
          linarith
      _ = (128 / Real.log 2 + 2 * (48 / c ^ 4)) * 2 ^ j / ((j:ℝ) + 1) := by ring
      _ ≤ _ := by gcongr; linarith

/-- The summand `Λ(1 + m q) / (1 + m q)`. -/
def apSummand (q m : ℕ) : ℝ := Λ (1 + m * q) / ((1 + m * q : ℕ) : ℝ)

lemma apSummand_nonneg (q m : ℕ) : 0 ≤ apSummand q m :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

/-- A block `M ≤ m < 2M` of the progression contributes at most
`#(prime powers) · log(2Mq)/(Mq)`. -/
lemma block_sum_le {q : ℕ} (hq : 0 < q) {M : ℕ} (hM : 0 < M) :
    ∑ m ∈ Finset.Ico M (2 * M), apSummand q m ≤
      (#{m ∈ Finset.range M | IsPrimePow (apTerm q M m)} : ℝ) *
        (Real.log (2 * M * q) / (M * q)) := by
  rw [Finset.sum_Ico_eq_sum_range, show 2 * M - M = M by omega, Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hkM := Finset.mem_range.mp hk
  obtain ⟨h1, h2⟩ := apTerm_mem hq hkM
  have happ : apSummand q (M + k) = Λ (apTerm q M k) / (apTerm q M k : ℝ) := rfl
  rw [happ]
  have hMq : (0:ℝ) < (M:ℝ) * q := by positivity
  split_ifs with hpp
  · have hn0 : (0:ℝ) < apTerm q M k := by exact_mod_cast (by omega : 0 < apTerm q M k)
    have h2' : (apTerm q M k : ℝ) ≤ 2 * M * q := by
      have : (apTerm q M k : ℝ) ≤ ((2 * (M * q) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith
    have hΛ : Λ (apTerm q M k) ≤ Real.log (2 * M * q) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 h2')
    have hn : (M:ℝ) * q ≤ apTerm q M k := by exact_mod_cast h1.le
    have hlog0 : 0 ≤ Real.log (2 * M * q) := Real.log_nonneg (by
      have : (1:ℝ) ≤ M * q := by
        have : 1 ≤ M * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
        exact_mod_cast this
      linarith)
    rw [one_mul]
    calc Λ (apTerm q M k) / (apTerm q M k : ℝ)
        ≤ Real.log (2 * M * q) / (apTerm q M k : ℝ) := by gcongr
      _ ≤ Real.log (2 * M * q) / (M * q) := div_le_div_of_nonneg_left hlog0 hMq hn
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]; simp

/-- Splitting `[0, 2^J)` into the dyadic blocks `[2^j, 2^{j+1})`. -/
lemma sum_range_pow_two (g : ℕ → ℝ) (hg0 : g 0 = 0) (J : ℕ) :
    ∑ m ∈ Finset.range (2 ^ J), g m =
      ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), g m := by
  induction J with
  | zero => simp [hg0]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, mul_comm (2 ^ J) 2,
      Finset.sum_range_add_sum_Ico _ (by omega : 2 ^ J ≤ 2 * 2 ^ J)]

/-- The sum over `n ≡ 1 mod q`, `n ≤ N`, is a sum over the progression `1 + m q`, `m < L`. -/
lemma sum_progression_le {q : ℕ} (hq : 0 < q) (N L : ℕ) (hNL : N < 1 + L * q) :
    ∑ n ∈ Finset.Ioc 0 N, (if (n : ZMod q) = 1 then Λ n / n else 0) ≤
      ∑ m ∈ Finset.range L, apSummand q m := by
  rw [← Finset.sum_filter]
  have hsub : (Finset.Ioc 0 N).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = 1) ⊆
      (Finset.range L).image (fun m : ℕ => 1 + m * q) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, hnN⟩, hn1⟩ := hn
    rw [Finset.mem_image]
    have hdvd : q ∣ n - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), hn1, Nat.cast_one, sub_self]
    obtain ⟨m, hm⟩ := hdvd
    have hcomm : q * m = m * q := Nat.mul_comm q m
    refine ⟨m, ?_, by omega⟩
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    have : L * q ≤ m * q := Nat.mul_le_mul_right q h
    omega
  have hinj : Set.InjOn (fun m : ℕ => 1 + m * q) (Finset.range L : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    exact Nat.eq_of_mul_eq_mul_right hq (by omega)
  calc ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = 1), Λ n / n
      ≤ ∑ n ∈ (Finset.range L).image (fun m : ℕ => 1 + m * q), Λ n / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
    _ = ∑ m ∈ Finset.range L, apSummand q m := by
        rw [Finset.sum_image hinj]; rfl

lemma sum_inv_eq_harmonic (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j:ℝ) + 1)⁻¹ = (harmonic J : ℝ) := by
  simp [harmonic]

/-- The dyadic blocks up to `2^{16(L+1)}`, `L = ⌊log₂ q⌋`, cover the progression up to `q^17`. -/
lemma progression_cover {q : ℕ} (hq0 : 0 < q) :
    q ^ 17 < 1 + 2 ^ (16 * (Nat.log 2 q + 1)) * q := by
  have hqL : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have h1 : q ^ 16 < 2 ^ (16 * (Nat.log 2 q + 1)) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_lt_pow_left hqL (by norm_num)
  have h2 : q ^ 16 * q < 2 ^ (16 * (Nat.log 2 q + 1)) * q := Nat.mul_lt_mul_of_pos_right h1 hq0
  have h3 : q ^ 17 = q ^ 16 * q := by ring
  omega

/-- Every block below `2^{16(L+1)}` satisfies the sieve condition `2^{j/32} < q`. -/
lemma progression_cond {q : ℕ} (hq : 2 ≤ q) {j : ℕ} (hj : j < 16 * (Nat.log 2 q + 1)) :
    (2:ℝ) ^ ((j:ℝ) / 32) < q := by
  have hqL : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hLq : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hnat : 2 ^ j < q ^ 32 := by
    calc 2 ^ j < 2 ^ (16 * (Nat.log 2 q + 1)) := Nat.pow_lt_pow_right (by norm_num) hj
      _ = (2 ^ (Nat.log 2 q + 1)) ^ 16 := by rw [← pow_mul, mul_comm]
      _ ≤ (q ^ 2) ^ 16 := by
          apply Nat.pow_le_pow_left
          rw [pow_succ, sq]
          exact Nat.mul_le_mul hLq hq
      _ = q ^ 32 := by rw [← pow_mul]
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hreal : ((2:ℝ) ^ ((j:ℝ) / 32)) ^ (32 : ℕ) < (q:ℝ) ^ (32 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (j:ℝ) / 32 * ((32 : ℕ) : ℝ) = (j : ℕ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
    exact_mod_cast hnat
  exact lt_of_pow_lt_pow_left₀ 32 hqpos.le hreal

/-- The contribution of one dyadic block. -/
lemma block_contrib {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hblock : ∀ (q : ℕ), q.Prime → ∀ j : ℕ, (2:ℝ) ^ ((j:ℝ) / 32) < q →
      (#{m ∈ Finset.range (2 ^ j) | IsPrimePow (apTerm q (2 ^ j) m)} : ℝ) ≤
        C₁ * 2 ^ j / ((j:ℝ) + 1))
    {q : ℕ} (hq : q.Prime) {j : ℕ} (hcond : (2:ℝ) ^ ((j:ℝ) / 32) < q) :
    ∑ m ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), apSummand q m ≤
      C₁ / q * (Real.log 2 + Real.log q / ((j:ℝ) + 1)) := by
  have hq0 : 0 < q := hq.pos
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq0
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq0
  have h2j0 : 0 < 2 ^ j := pow_pos (by norm_num) j
  have h1 := block_sum_le hq0 h2j0
  have h2 := hblock q hq j hcond
  have hj1 : (0:ℝ) < (j:ℝ) + 1 := by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
  have h2j : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hcast : (((2 ^ j : ℕ)) : ℝ) = 2 ^ j := by push_cast; rfl
  rw [hcast] at h1
  have hlogpos : 0 ≤ Real.log (2 * 2 ^ j * q) / (2 ^ j * q) := by
    apply div_nonneg _ (by positivity)
    apply Real.log_nonneg
    nlinarith
  have hlogexp : Real.log (2 * 2 ^ j * q) = ((j:ℝ) + 1) * Real.log 2 + Real.log q := by
    rw [Real.log_mul (by positivity) hqpos.ne', ← pow_succ', Real.log_pow]
    push_cast; ring
  calc ∑ m ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), apSummand q m
      ≤ (#{m ∈ Finset.range (2 ^ j) | IsPrimePow (apTerm q (2 ^ j) m)} : ℝ) *
          (Real.log (2 * 2 ^ j * q) / (2 ^ j * q)) := h1
    _ ≤ C₁ * 2 ^ j / ((j:ℝ) + 1) * (Real.log (2 * 2 ^ j * q) / (2 ^ j * q)) :=
        mul_le_mul_of_nonneg_right h2 hlogpos
    _ = C₁ / q * (Real.log 2 + Real.log q / ((j:ℝ) + 1)) := by
        rw [hlogexp]; field_simp

/-- The harmonic sum over the blocks. -/
lemma blocks_harmonic (J : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    ∑ j ∈ Finset.range J, y / ((j:ℝ) + 1) ≤ y * (1 + Real.log J) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum, sum_inv_eq_harmonic]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J) hy

/-- The progression sum, before the final simplification. -/
lemma sum_progression_le_blocks {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hblock : ∀ (q : ℕ), q.Prime → ∀ j : ℕ, (2:ℝ) ^ ((j:ℝ) / 32) < q →
      (#{m ∈ Finset.range (2 ^ j) | IsPrimePow (apTerm q (2 ^ j) m)} : ℝ) ≤
        C₁ * 2 ^ j / ((j:ℝ) + 1))
    {q : ℕ} (hq : q.Prime) :
    ∑ n ∈ Finset.Ioc 0 (q ^ 17), (if (n : ZMod q) = 1 then Λ n / n else 0) ≤
      C₁ / q * (((16 * (Nat.log 2 q + 1) : ℕ) : ℝ) * Real.log 2 +
        Real.log q * (1 + Real.log ((16 * (Nat.log 2 q + 1) : ℕ) : ℝ))) := by
  have hq0 : 0 < q := hq.pos
  set J := 16 * (Nat.log 2 q + 1) with hJ
  have hsum := sum_progression_le hq0 (q ^ 17) (2 ^ J) (progression_cover hq0)
  rw [sum_range_pow_two (apSummand q) (by simp [apSummand]) J] at hsum
  have hblk : ∀ j ∈ Finset.range J,
      ∑ m ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), apSummand q m ≤
        C₁ / q * (Real.log 2 + Real.log q / ((j:ℝ) + 1)) := fun j hj =>
    block_contrib hC₁ hblock hq (progression_cond hq.two_le (Finset.mem_range.mp hj))
  have hsum2 := hsum.trans (Finset.sum_le_sum hblk)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum2
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq0)
  have hharm := blocks_harmonic J (Real.log q) hlq
  have hCq : 0 ≤ C₁ / q := by positivity
  calc _ ≤ _ := hsum2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hCq

/-- `16(⌊log₂ q⌋ + 1) ≤ a log q` with `a = 16(1/log 2 + 1)`, for `q ≥ 3`. -/
lemma blocks_count_le {q : ℕ} (hq3 : 3 ≤ q) :
    (((16 * (Nat.log 2 q + 1) : ℕ) : ℝ)) ≤ 16 * (1 / Real.log 2 + 1) * Real.log q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq3
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlq : 1 ≤ Real.log q := (lt_of_lt_of_le hl3 (Real.log_le_log (by norm_num) hqR)).le
  have hLq : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hLreal : ((Nat.log 2 q : ℕ) : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hLq)
  have hL' : ((Nat.log 2 q : ℕ) : ℝ) ≤ Real.log q / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; exact hLreal
  push_cast
  have : 1 / Real.log 2 * Real.log q = Real.log q / Real.log 2 := by ring
  nlinarith

/-- **The progression sum.** For `q` prime, `q ≥ 3`,
`∑_{n ≤ q^17, n ≡ 1 (q)} Λ(n)/n ≤ C log q log log q / q`. -/
theorem sum_progression_bound : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, q.Prime → 3 ≤ q →
    ∑ n ∈ Finset.Ioc 0 (q ^ 17), (if (n : ZMod q) = 1 then Λ n / n else 0) ≤
      C * Real.log q * Real.log (Real.log q) / q := by
  obtain ⟨C₁, hC₁, hblock⟩ := block_count_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha1 : 1 < 16 * (1 / Real.log 2 + 1) := by
    have : 0 < 1 / Real.log 2 := by positivity
    linarith
  have hloga : 0 < Real.log (16 * (1 / Real.log 2 + 1)) := Real.log_pos ha1
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hℓ₀ : 0 < Real.log (Real.log 3) := Real.log_pos hl3
  refine ⟨C₁ * ((16 * (1 / Real.log 2 + 1) * Real.log 2 + 1 +
      Real.log (16 * (1 / Real.log 2 + 1))) / Real.log (Real.log 3) + 1), by positivity, ?_⟩
  intro q hq hq3
  have hmain := sum_progression_le_blocks hC₁ hblock hq
  have hJa := blocks_count_le hq3
  have hJpos : (0:ℝ) < ((16 * (Nat.log 2 q + 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  generalize ((16 * (Nat.log 2 q + 1) : ℕ) : ℝ) = J at hmain hJa hJpos
  set a : ℝ := 16 * (1 / Real.log 2 + 1) with ha
  set ℓ₀ : ℝ := Real.log (Real.log 3) with hℓ₀def
  set B : ℝ := a * Real.log 2 + 1 + Real.log a with hBdef
  have hB0 : 0 < B := by positivity
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq3
  have hqpos : (0:ℝ) < q := by linarith
  have hlq : 1 < Real.log q := lt_of_lt_of_le hl3 (Real.log_le_log (by norm_num) hqR)
  have hlq0 : 0 < Real.log q := by linarith
  set ℓ : ℝ := Real.log (Real.log q) with hℓdef
  have hℓℓ : ℓ₀ ≤ ℓ := Real.log_le_log (by linarith) (Real.log_le_log (by norm_num) hqR)
  have hlogJ : Real.log J ≤ Real.log a + ℓ :=
    (Real.log_le_log hJpos hJa).trans_eq (Real.log_mul (by positivity) hlq0.ne')
  have hfin : J * Real.log 2 + Real.log q * (1 + Real.log J) ≤
      (B / ℓ₀ + 1) * (Real.log q * ℓ) := by
    have e1 : J * Real.log 2 ≤ a * Real.log 2 * Real.log q := by
      have := mul_le_mul_of_nonneg_right hJa hlog2.le
      linarith
    have e2 : Real.log q * (1 + Real.log J) ≤ Real.log q * (1 + Real.log a + ℓ) := by
      apply mul_le_mul_of_nonneg_left _ hlq0.le; linarith
    have e3 : B * Real.log q ≤ B / ℓ₀ * (Real.log q * ℓ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hℓ₀]
      have : B * Real.log q * ℓ₀ ≤ B * Real.log q * ℓ :=
        mul_le_mul_of_nonneg_left hℓℓ (by positivity)
      linarith
    have e4 : B * Real.log q = a * Real.log 2 * Real.log q + Real.log q * (1 + Real.log a) := by
      rw [hBdef]; ring
    nlinarith
  have hCq : 0 ≤ C₁ / q := by positivity
  calc _ ≤ C₁ / q * (J * Real.log 2 + Real.log q * (1 + Real.log J)) := hmain
    _ ≤ C₁ / q * ((B / ℓ₀ + 1) * (Real.log q * ℓ)) := mul_le_mul_of_nonneg_left hfin hCq
    _ = C₁ * (B / ℓ₀ + 1) * Real.log q * ℓ / q := by ring

end Vinogradov.EulerKronecker
