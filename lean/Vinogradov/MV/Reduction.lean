import Vinogradov.MV.Bilinear

/-!
# Reduction to a bilinear sum over primes

For `f` completely multiplicative with `|f| ≤ 1`,
`S log N = ∑_{p ≤ N} log p f(p) ∑_{m ≤ N/p} f(m) e(pmα) + O(N)`, where `S = ∑_{n ≤ N} f(n) e(nα)`:
`log n = ∑_{d ∣ n} Λ(d)`, `∑_{n ≤ N} log(N/n) ≤ N`, and the prime powers `p^k`, `k ≥ 2`, contribute
`O(N)`.
-/

namespace Vinogradov.MV

open Finset Complex Vinogradov.PV ArithmeticFunction


theorem sum_log_eq (N : ℕ) : ∑ n ∈ Ioc 0 N, Real.log n = Real.log N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos N).ne')]
    ring

theorem sum_log_div_le (N : ℕ) : ∑ n ∈ Ioc 0 N, (Real.log N - Real.log n) ≤ N := by
  rw [sum_sub_distrib, sum_const, Nat.card_Ioc, sum_log_eq, nsmul_eq_mul, Nat.sub_zero]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hp : (0 : ℝ) < (N : ℝ) ^ N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hp.ne' hf.ne', Real.log_pow] at this
  linarith

/-- `∑_{n ≤ N} ∑_{d ∣ n} G(d, n) = ∑_{d ≤ N} ∑_{m ≤ N/d} G(d, dm)`. -/
theorem sum_divisors_swap (N : ℕ) (G : ℕ → ℕ → ℂ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, G d n =
      ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), G d (d * m) := by
  rw [sum_comm' (t' := Ioc 0 N) (s' := fun d => (Ioc 0 N).filter (d ∣ ·))]
  · apply sum_congr rfl; intro d hd
    rw [mem_Ioc] at hd
    have himg : (Ioc 0 N).filter (d ∣ ·) = (Ioc 0 (N / d)).image (d * ·) := by
      ext n
      simp only [mem_filter, mem_Ioc, mem_image]
      constructor
      · rintro ⟨⟨hn0, hnN⟩, m, rfl⟩
        refine ⟨m, ⟨Nat.pos_of_mul_pos_left hn0, ?_⟩, rfl⟩
        rw [Nat.le_div_iff_mul_le hd.1, mul_comm]; exact hnN
      · rintro ⟨m, ⟨hm0, hmN⟩, rfl⟩
        rw [Nat.le_div_iff_mul_le hd.1, mul_comm] at hmN
        exact ⟨⟨Nat.mul_pos hd.1 hm0, hmN⟩, dvd_mul_right d m⟩
    rw [himg, sum_image]
    intro x _ y _ hxy; exact Nat.eq_of_mul_eq_mul_left hd.1 hxy
  · intro n d
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have := Nat.le_of_dvd hn0 hdn
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn hn0, le_trans this hnN⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩

/-- `log n ≤ 2 √n`, so `log n / n² ≤ 2 n^{-3/2}`. -/
theorem log_div_sq_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log n / (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_le_rpow_div (x := (n : ℝ)) hn0.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsq : (n : ℝ) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast]; norm_num
  rw [hsq, div_le_iff₀ (by positivity)]
  have h1 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  calc Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := hl
    _ = 2 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
      field_simp

/-- **Prime powers.** `∑_{d ≤ N, d not prime} Λ(d)/d ≤ C`. -/
theorem prime_power_tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    ∑ d ∈ Ioc 0 N with ¬ d.Prime, Λ d / d ≤ C := by
  have hsum : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 4
  refine ⟨∑' n : ℕ, 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹, tsum_nonneg fun n => by positivity, ?_⟩
  intro N
  set T := ((Icc 2 N).filter Nat.Prime) ×ˢ (Icc 2 N) with hT
  set φ : ℕ × ℕ → ℕ := fun x => x.1 ^ x.2 with hφ
  have hinj : Set.InjOn φ ↑T := by
    intro x hx y hy hxy
    rw [mem_coe, hT, mem_product, mem_filter, mem_Icc, mem_Icc] at hx hy
    have hx2 : 1 ≤ x.2 := by omega
    have hy2 : 1 ≤ y.2 := by omega
    have h1 : x.1 ^ (x.2 - 1 + 1) = y.1 ^ (y.2 - 1 + 1) := by
      rw [Nat.sub_add_cancel hx2, Nat.sub_add_cancel hy2]; exact hxy
    obtain ⟨h2, h3⟩ := Nat.Prime.pow_inj hx.1.2 hy.1.2 h1
    exact Prod.ext h2 (by omega)
  have hsub : ((Ioc 0 N).filter (fun d => ¬ d.Prime)).filter IsPrimePow ⊆ T.image φ := by
    intro d hd
    simp only [mem_filter, mem_Ioc] at hd
    obtain ⟨⟨⟨hd0, hdN⟩, hnp⟩, hpp⟩ := hd
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      rw [this, pow_one] at hnp; exact hnp hp
    rw [mem_image]
    refine ⟨(p, k), ?_, rfl⟩
    simp only [hT, mem_product, mem_filter, mem_Icc]
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hkp : k < p ^ k := Nat.lt_pow_self hp.one_lt
    exact ⟨⟨⟨hp.two_le, by omega⟩, hp⟩, hk2, by omega⟩
  have hnn : ∀ d : ℕ, 0 ≤ Λ d / (d : ℝ) := fun d => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d)
  calc ∑ d ∈ Ioc 0 N with ¬ d.Prime, Λ d / d
      = ∑ d ∈ ((Ioc 0 N).filter (fun d => ¬ d.Prime)).filter IsPrimePow, Λ d / d := by
        rw [sum_filter (p := IsPrimePow)]
        apply sum_congr rfl; intro d _
        split_ifs with h
        · rfl
        · rw [vonMangoldt_eq_zero_iff.2 h, zero_div]
    _ ≤ ∑ d ∈ T.image φ, Λ d / d := sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hnn d)
    _ = ∑ x ∈ T, Λ (x.1 ^ x.2) / ((x.1 ^ x.2 : ℕ) : ℝ) :=
        sum_image (f := fun d : ℕ => Λ d / (d : ℝ)) hinj
    _ = ∑ p ∈ (Icc 2 N).filter Nat.Prime, Real.log p * ∑ k ∈ Icc 2 N, (1 / (p : ℝ)) ^ k := by
        rw [hT, sum_product]
        apply sum_congr rfl; intro p hp
        rw [mem_filter] at hp
        rw [mul_sum]
        apply sum_congr rfl; intro k hk
        rw [mem_Icc] at hk
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp.2]
        push_cast; rw [one_div_pow, one_div, div_eq_mul_inv]
    _ ≤ ∑ p ∈ (Icc 2 N).filter Nat.Prime, Real.log p * (2 * (1 / (p : ℝ)) ^ 2) := by
        apply sum_le_sum; intro p hp
        rw [mem_filter, mem_Icc] at hp
        apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.1
        have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
        have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
        have hg := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) hx0 (by linarith)
        have hI : Icc 2 N = Ico 2 (N + 1) := rfl
        rw [hI]
        calc ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k ≤ (1 / (p : ℝ)) ^ 2 / (1 - 1 / p) := hg
          _ ≤ (1 / (p : ℝ)) ^ 2 / (1 / 2) := by
              apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
          _ = 2 * (1 / (p : ℝ)) ^ 2 := by ring
    _ ≤ ∑ n ∈ Icc 2 N, 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
        refine le_trans (sum_le_sum fun p hp => ?_) (sum_le_sum_of_subset_of_nonneg
          (filter_subset _ _) (fun n _ _ => by positivity))
        rw [mem_filter, mem_Icc] at hp
        have := log_div_sq_le (n := p) (by omega)
        calc Real.log p * (2 * (1 / (p : ℝ)) ^ 2) = 2 * (Real.log p / (p : ℝ) ^ 2) := by
              field_simp
          _ ≤ 2 * (2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by gcongr
          _ = 4 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by ring
    _ ≤ ∑' n : ℕ, 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
        hsum.sum_le_tsum _ (fun n _ => by positivity)

/-- **Reduction.** -/
theorem reduction : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ m n, f (m * n) = f m * f n) →
    (∀ n, ‖f n‖ ≤ 1) → ∀ (α : ℝ) (N : ℕ),
    ‖(∑ n ∈ Ioc 0 N, f n * e (n * α)) * (Real.log N : ℂ) -
      ∑ p ∈ Ioc 0 N with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤ C * N := by
  obtain ⟨C₀, hC₀, htail⟩ := prime_power_tail
  refine ⟨1 + C₀, by linarith, ?_⟩
  intro f hfm hfb α N
  -- `S log N = ∑ f(n) e(nα) log n + ∑ f(n) e(nα) log(N/n)`
  have h1 : (∑ n ∈ Ioc 0 N, f n * e (n * α)) * (Real.log N : ℂ) =
      ∑ n ∈ Ioc 0 N, f n * e (n * α) * (Real.log n : ℂ) +
        ∑ n ∈ Ioc 0 N, f n * e (n * α) * ((Real.log N - Real.log n : ℝ) : ℂ) := by
    rw [sum_mul, ← sum_add_distrib]
    apply sum_congr rfl; intro n _; push_cast; ring
  -- `∑ f(n) e(nα) log n = ∑_{d ≤ N} Λ(d) f(d) ∑_{m ≤ N/d} f(m) e(dmα)`
  have h2 : ∑ n ∈ Ioc 0 N, f n * e (n * α) * (Real.log n : ℂ) =
      ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α) := by
    have : ∀ n : ℕ, f n * e (n * α) * (Real.log n : ℂ) =
        ∑ d ∈ n.divisors, (Λ d : ℂ) * (f n * e (n * α)) := by
      intro n
      rw [← sum_mul, ← vonMangoldt_sum]; push_cast; ring
    simp_rw [this]
    rw [sum_divisors_swap N (fun d n => (Λ d : ℂ) * (f n * e (n * α)))]
    apply sum_congr rfl; intro d _
    rw [mul_sum]
    apply sum_congr rfl; intro m _
    rw [hfm]; push_cast; ring
  -- split `d` prime / not prime
  have h3 : ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α) =
      ∑ p ∈ Ioc 0 N with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α) +
      ∑ d ∈ Ioc 0 N with ¬ d.Prime, (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α) := by
    rw [← sum_filter_add_sum_filter_not (Ioc 0 N) Nat.Prime]
    congr 1
    apply sum_congr rfl; intro p hp
    rw [mem_filter] at hp
    rw [vonMangoldt_apply_prime hp.2]
  have hnp : ‖∑ d ∈ Ioc 0 N with ¬ d.Prime,
      (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α)‖ ≤ C₀ * N := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ d ∈ Ioc 0 N with ¬ d.Prime,
          ‖(Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α)‖
        ≤ ∑ d ∈ Ioc 0 N with ¬ d.Prime, N * (Λ d / d) := by
          apply sum_le_sum; intro d hd
          rw [mem_filter, mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1.1
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg vonMangoldt_nonneg]
          have hin : ‖∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α)‖ ≤ N / d := by
            refine le_trans (norm_sum_le _ _) ?_
            calc ∑ m ∈ Ioc 0 (N / d), ‖f m * e (d * m * α)‖
                ≤ ∑ m ∈ Ioc 0 (N / d), (1 : ℝ) := by
                  apply sum_le_sum; intro m _; rw [norm_mul, norm_e, mul_one]; exact hfb m
              _ = ((N / d : ℕ) : ℝ) := by simp
              _ ≤ N / d := Nat.cast_div_le
          calc Λ d * ‖f d‖ * ‖∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α)‖
              ≤ Λ d * 1 * (N / d) := by
                gcongr
                exact hfb d
            _ = N * (Λ d / d) := by ring
      _ = N * ∑ d ∈ Ioc 0 N with ¬ d.Prime, Λ d / d := by rw [mul_sum]
      _ ≤ N * C₀ := by gcongr; exact htail N
      _ = C₀ * N := by ring
  have hlog : ‖∑ n ∈ Ioc 0 N, f n * e (n * α) * ((Real.log N - Real.log n : ℝ) : ℂ)‖ ≤ N := by
    refine le_trans (norm_sum_le _ _) (le_trans ?_ (sum_log_div_le N))
    apply sum_le_sum; intro n hn
    rw [mem_Ioc] at hn
    have hlogle : Real.log n ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    rw [norm_mul, norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    calc ‖f n‖ * (Real.log N - Real.log n) ≤ 1 * (Real.log N - Real.log n) := by
          apply mul_le_mul_of_nonneg_right (hfb n) (by linarith)
      _ = _ := one_mul _
  rw [h1, h2, h3]
  calc ‖(∑ p ∈ Ioc 0 N with p.Prime,
          (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α) +
        ∑ d ∈ Ioc 0 N with ¬ d.Prime,
          (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α)) +
        ∑ n ∈ Ioc 0 N, f n * e (n * α) * ((Real.log N - Real.log n : ℝ) : ℂ) -
        ∑ p ∈ Ioc 0 N with p.Prime,
          (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖
      = ‖∑ d ∈ Ioc 0 N with ¬ d.Prime,
          (Λ d : ℂ) * f d * ∑ m ∈ Ioc 0 (N / d), f m * e (d * m * α) +
        ∑ n ∈ Ioc 0 N, f n * e (n * α) * ((Real.log N - Real.log n : ℝ) : ℂ)‖ := by
        congr 1; ring
    _ ≤ C₀ * N + N := le_trans (norm_add_le _ _) (add_le_add hnp hlog)
    _ = (1 + C₀) * N := by ring

end Vinogradov.MV
