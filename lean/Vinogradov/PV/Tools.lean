import Mathlib

/-!
# Elementary tools

Abel summation in the discrete form, the additive character `e(x) = exp(2πix)`, and the bounds
`∑_{3 ≤ n ≤ N} 1/(n log n) ≤ log log N` and `∑_{m ≤ M} m^{-19/20} ≤ 20 M^{1/20}`.
-/

namespace Vinogradov.PV

open Complex Finset

/-- **Abel summation.** With `A(n) = ∑_{M < k ≤ n} a(k)`,
`∑_{M < n ≤ N} a(n) g(n) = A(N) g(N) - ∑_{M ≤ n < N} A(n) (g(n+1) - g(n))`. -/
theorem abel_identity (a g : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Ioc M N, a n * g n =
      (∑ k ∈ Ioc M N, a k) * g N -
        ∑ n ∈ Ico M N, (∑ k ∈ Ioc M n, a k) * (g (n + 1) - g n) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [sum_Ioc_succ_top hMN, ih, sum_Ico_succ_top hMN, sum_Ioc_succ_top hMN]
    ring

/-- **Abel's inequality.** If `‖∑_{M < k ≤ n} a(k)‖ ≤ B` for `M ≤ n ≤ N`, then
`‖∑_{M < n ≤ N} a(n) g(n)‖ ≤ B (‖g(N)‖ + ∑_{M ≤ n < N} ‖g(n+1) - g(n)‖)`. -/
theorem abel_bound (a g : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) {B : ℝ}
    (hB : ∀ n, M ≤ n → n ≤ N → ‖∑ k ∈ Ioc M n, a k‖ ≤ B) :
    ‖∑ n ∈ Ioc M N, a n * g n‖ ≤
      B * (‖g N‖ + ∑ n ∈ Ico M N, ‖g (n + 1) - g n‖) := by
  rw [abel_identity a g hMN]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB M le_rfl hMN)
  calc _ ≤ ‖(∑ k ∈ Ioc M N, a k) * g N‖ +
        ‖∑ n ∈ Ico M N, (∑ k ∈ Ioc M n, a k) * (g (n + 1) - g n)‖ := norm_sub_le _ _
    _ ≤ B * ‖g N‖ + ∑ n ∈ Ico M N, B * ‖g (n + 1) - g n‖ := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hB N hMN le_rfl) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
          obtain ⟨h1, h2⟩ := mem_Ico.mp hn
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hB n h1 h2.le) (norm_nonneg _)
    _ = _ := by rw [← mul_sum, mul_add]

/-- The additive character `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_zero : e 0 = 1 := by simp [e]

theorem norm_e_sub_one (x : ℝ) : ‖e x - 1‖ ≤ 2 * Real.pi * |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * x)
  have he : e x = Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    unfold e; congr 1; push_cast; ring
  rw [he]
  calc _ ≤ ‖(2 * Real.pi * x : ℝ)‖ := h
    _ = 2 * Real.pi * |x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos]

theorem norm_e_sub (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, ← e_add]; ring_nf
  rw [this, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one _

/-- `1/(n log n) ≤ log log n - log log (n - 1)` for `n ≥ 3`. -/
theorem inv_mul_log_le {n : ℕ} (hn : 3 ≤ n) :
    1 / ((n : ℝ) * Real.log n) ≤ Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  have h1 : 1 < (n : ℝ) - 1 := by linarith
  have hl1 : 0 < Real.log ((n : ℝ) - 1) := Real.log_pos h1
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  -- `log n - log (n - 1) ≥ 1/n`
  have hd : 1 / (n : ℝ) ≤ Real.log n - Real.log ((n : ℝ) - 1) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have h := Real.one_sub_inv_le_log_of_pos (x := (n : ℝ) / (n - 1)) (by positivity)
    have : 1 - ((n : ℝ) / (n - 1))⁻¹ = 1 / n := by
      field_simp; ring
    linarith
  -- `log (log n / log (n - 1)) ≥ 1 - log (n - 1) / log n`
  have hq := Real.one_sub_inv_le_log_of_pos (x := Real.log n / Real.log ((n : ℝ) - 1))
    (by positivity)
  rw [Real.log_div hl.ne' hl1.ne'] at hq
  have h2 : 1 - (Real.log n / Real.log ((n : ℝ) - 1))⁻¹ =
      (Real.log n - Real.log ((n : ℝ) - 1)) / Real.log n := by
    field_simp
  rw [h2] at hq
  have h3 : 1 / ((n : ℝ) * Real.log n) ≤ (Real.log n - Real.log ((n : ℝ) - 1)) / Real.log n := by
    rw [one_div, mul_inv, ← one_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr hl.le)
  linarith

/-- `∑_{2 < n ≤ N} 1/(n log n) ≤ log log N - log log 2` for `N ≥ 2`. -/
theorem sum_inv_mul_log_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ioc 2 N, 1 / ((n : ℝ) * Real.log n) ≤
      Real.log (Real.log N) - Real.log (Real.log 2) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ioc_succ_top hN]
    have h := inv_mul_log_le (n := N + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    push_cast at h ⊢
    linarith

/-- `log log 2 ≥ -1`. -/
theorem log_log_two_ge : -1 ≤ Real.log (Real.log 2) := by
  have h := Real.add_one_le_exp (-1)
  have h2 : Real.exp (-1) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    have h3 : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9
      linarith
    linarith
  calc (-1 : ℝ) = Real.log (Real.exp (-1)) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) h2

/-- `∑_{0 < n ≤ N} 1/(n log n) ≤ 3 + log log N`. -/
theorem sum_inv_mul_log_le' (N : ℕ) :
    ∑ n ∈ Ioc 0 N, 1 / ((n : ℝ) * Real.log n) ≤ 3 + Real.log (Real.log N) := by
  have h12 : ∀ n ∈ Ioc (0 : ℕ) 2, 1 / ((n : ℝ) * Real.log n) ≤ 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
    interval_cases n
    · simp
    · simp only [Nat.cast_ofNat]
      rw [div_le_one (by positivity)]
      have := Real.log_two_gt_d9; linarith
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp
  · rw [← sum_Ioc_consecutive _ (Nat.zero_le 2) hN]
    have hA : ∑ n ∈ Ioc (0 : ℕ) 2, 1 / ((n : ℝ) * Real.log n) ≤ 2 := by
      calc _ ≤ ∑ n ∈ Ioc (0 : ℕ) 2, (1 : ℝ) := sum_le_sum h12
        _ = 2 := by simp
    have := sum_inv_mul_log_le hN
    have := log_log_two_ge
    linarith

/-- `∑_{0 < m ≤ M} m^{-19/20} ≤ 20 M^{1/20}`. -/
theorem sum_rpow_le (M : ℕ) :
    ∑ m ∈ Ioc 0 M, ((m : ℝ) ^ (19 / 20 : ℝ))⁻¹ ≤ 20 * (M : ℝ) ^ (1 / 20 : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le M)]
    -- `(M+1)^{-19/20} ≤ 20 ((M+1)^{1/20} - M^{1/20})`
    set x : ℝ := ((M + 1 : ℕ) : ℝ) with hxdef
    have hx : 1 ≤ x := by rw [hxdef]; exact_mod_cast Nat.succ_pos M
    have hx0 : 0 < x := by linarith
    have hM : (M : ℝ) = x * (1 + (-1 / x)) := by
      rw [hxdef]; push_cast; field_simp; ring
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / x)
      (by rw [neg_div, neg_le_neg_iff, div_le_one hx0]; exact hx) (p := 1 / 20)
      (by norm_num) (by norm_num)
    have hMp : (M : ℝ) ^ (1 / 20 : ℝ) ≤ x ^ (1 / 20 : ℝ) - (1 / 20) * x ^ (-(19 / 20) : ℝ) := by
      rw [hM, Real.mul_rpow hx0.le (by
        have : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
        rw [neg_div]; linarith)]
      have hxp : 0 ≤ x ^ (1 / 20 : ℝ) := by positivity
      calc x ^ (1 / 20 : ℝ) * (1 + -1 / x) ^ (1 / 20 : ℝ)
          ≤ x ^ (1 / 20 : ℝ) * (1 + 1 / 20 * (-1 / x)) := mul_le_mul_of_nonneg_left hb hxp
        _ = x ^ (1 / 20 : ℝ) - (1 / 20) * (x ^ (1 / 20 : ℝ) * x⁻¹) := by ring
        _ = x ^ (1 / 20 : ℝ) - (1 / 20) * x ^ (-(19 / 20) : ℝ) := by
            congr 2
            rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
            norm_num
    have hinv : (x ^ (19 / 20 : ℝ))⁻¹ = x ^ (-(19 / 20) : ℝ) := by
      rw [Real.rpow_neg hx0.le]
    rw [hinv]
    linarith

end Vinogradov.PV
