import Vinogradov.CharacterSums

/-!
# Prime sums twisted by a character

For every nonprincipal Dirichlet character `ξ` modulo `m` and every `x ≥ 1`,
`‖∑_{p ≤ x} ξ(p) log p‖ ≤ C x^{19/20} log (m + 2)`, with `C` absolute. This follows from the
Riesz-mean bound `Vinogradov.Analytic.riesz_character_bound` and the zero-free half-plane
`re s > 7/8`.
-/

namespace Vinogradov.PV

open Complex
open scoped LSeries.notation ArithmeticFunction.vonMangoldt

/-- `h ‖∑_{n ≤ x} a(n)‖ ≤ ‖(x + h) R(x + h) - x R(x)‖ + B h (h + 1)` when `‖a(n)‖ ≤ B`
for `n ≤ x + h`. -/
theorem unsmooth (a : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : ∀ n : ℕ, (n : ℝ) ≤ x + h → ‖a n‖ ≤ B) :
    h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤
      ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x‖ +
        B * (h * (h + 1)) := by
  have hT : ∀ y : ℝ, 0 < y → (y : ℂ) * Riesz.rieszSum a y =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, a n * ((y : ℂ) - n) := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    unfold Riesz.rieszSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    field_simp
  have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit := Finset.sum_Ioc_consecutive (fun n => a n * (((x + h : ℝ) : ℂ) - n))
    (Nat.zero_le ⌊x⌋₊) hle
  have hmain : ((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x =
      (h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
    rw [hT (x + h) (by linarith), hT x hx, ← hsplit, Finset.mul_sum]
    have hs : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (((x + h : ℝ) : ℂ) - n) =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ((h : ℂ) * a n + a n * ((x : ℂ) - n)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      push_cast
      ring
    rw [hs, Finset.sum_add_distrib]
    ring
  have htail : ‖∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)‖ ≤
      B * (h * (h + 1)) := by
    calc _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, ‖a n * (((x + h : ℝ) : ℂ) - n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, B * h := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
          have hn1 : x < n := Nat.lt_of_floor_lt h1
          have hn2 : (n : ℝ) ≤ x + h := (Nat.le_floor_iff (by linarith)).mp h2
          have he : ((x + h : ℝ) : ℂ) - n = ((x + h - n : ℝ) : ℂ) := by push_cast; ring
          rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          exact mul_le_mul (ha n hn2) (by linarith) (by linarith) hB
      _ = ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) * (B * h) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (h + 1) * (B * h) := by
          gcongr
          rw [Nat.cast_sub hle]
          have h1 := Nat.floor_le (show 0 ≤ x + h by linarith)
          have h2 := Nat.lt_floor_add_one x
          linarith
      _ = B * (h * (h + 1)) := by ring
  have hS : (h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n =
      (((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x) -
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) := by
    rw [hmain]; ring
  calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ = ‖(h : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    _ ≤ _ := by
        rw [hS]
        exact (norm_sub_le _ _).trans (by gcongr)

/-- `log x ≤ 100 x^{1/100}` for `x ≥ 0`. -/
theorem log_le_rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 100 * x ^ (1 / 100 : ℝ) := by
  have := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 100 by norm_num)
  linarith [show x ^ (1 / 100 : ℝ) / (1 / 100) = 100 * x ^ (1 / 100 : ℝ) by ring]

/-- **Von Mangoldt sums.** `‖∑_{n ≤ x} ξ(n) Λ(n)‖ ≤ C x^{19/20} log (m + 2)`. -/
theorem vonMangoldt_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (ξ : DirichletCharacter ℂ m), ξ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (↗ξ * ↗Λ) n‖ ≤ C * x ^ (19 / 20 : ℝ) * Real.log (m + 2) := by
  obtain ⟨K, hK, hKb⟩ := Analytic.riesz_character_bound (e := 1 / 2000) (by norm_num)
    (by norm_num)
  refine ⟨16 * K + 1000, by positivity, ?_⟩
  intro m _ ξ hξ x hx
  have hx0 : 0 < x := by linarith
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hlog2 : Real.log 2 ≤ Real.log (m + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlog2' : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL : (1 / 2 : ℝ) ≤ Real.log (m + 2) := by linarith
  set σ : ℝ := 7 / 8 - 2 * (1 / 2000) + 8 * (1 / 2000) with hσ
  have hR : ∀ y : ℝ, 1 ≤ y → ‖Riesz.rieszSum (↗ξ * ↗Λ) y‖ ≤ K * y ^ σ * Real.log (m + 2) :=
    hKb m ξ hξ (7 / 8 - 2 * (1 / 2000)) (by norm_num) (by norm_num)
      (fun z hz => zeroFree m ξ hξ z (by linarith))
  set h : ℝ := x ^ (47 / 50 : ℝ) with hh
  have hh1 : 1 ≤ h := Real.one_le_rpow hx (by norm_num)
  have hh0 : 0 < h := by linarith
  have hhx : h ≤ x := by
    calc h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have hBa : ∀ n : ℕ, (n : ℝ) ≤ x + h → ‖(↗ξ * ↗Λ) n‖ ≤ Real.log (2 * x) := by
    intro n hn
    rw [Pi.mul_apply, norm_mul]
    have h1 : ‖(ξ n : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one ξ n
    have h2 : ‖((Λ n : ℝ) : ℂ)‖ ≤ Real.log (2 * x) := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp only [ArithmeticFunction.map_zero]
        exact Real.log_nonneg (by linarith)
      · calc Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log (2 * x) := Real.log_le_log (by exact_mod_cast hn0) (by linarith)
    calc ‖(ξ n : ℂ)‖ * ‖((Λ n : ℝ) : ℂ)‖ ≤ 1 * Real.log (2 * x) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hun := unsmooth (↗ξ * ↗Λ) hlog2x hx0 hh0 hBa
  have hdiff : ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) (x + h) -
      (x : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) x‖ ≤ 4 * x * (K * (2 * x) ^ σ * Real.log (m + 2)) := by
    have hσ0 : 0 ≤ σ := by norm_num [hσ]
    have hp : x ^ σ ≤ (2 * x) ^ σ := Real.rpow_le_rpow hx0.le (by linarith) hσ0
    have hp' : (x + h) ^ σ ≤ (2 * x) ^ σ := Real.rpow_le_rpow (by linarith) (by linarith) hσ0
    have hA := hR (x + h) (by linarith)
    have hB := hR x hx
    have hpos : 0 ≤ K * (2 * x) ^ σ * Real.log (m + 2) := by
      have : 0 ≤ Real.log (m + 2) := by linarith
      positivity
    calc _ ≤ ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) (x + h)‖ +
          ‖(x : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) x‖ := norm_sub_le _ _
      _ = (x + h) * ‖Riesz.rieszSum (↗ξ * ↗Λ) (x + h)‖ + x * ‖Riesz.rieszSum (↗ξ * ↗Λ) x‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos hx0]
      _ ≤ (2 * x) * (K * (2 * x) ^ σ * Real.log (m + 2)) +
            x * (K * (2 * x) ^ σ * Real.log (m + 2)) := by
          gcongr
          · nlinarith [norm_nonneg (Riesz.rieszSum (↗ξ * ↗Λ) (x + h))]
          · exact hA.trans (by gcongr)
          · exact hB.trans (by gcongr)
      _ ≤ 4 * x * (K * (2 * x) ^ σ * Real.log (m + 2)) := by nlinarith
  -- `(2x)^σ ≤ 2 x^σ` and `x^{1 + σ} / h = x^{σ + 3/50}` with `σ + 3/50 ≤ 19/20`
  have h2σ : (2 * x) ^ σ ≤ 2 * x ^ σ := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    gcongr
    calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by norm_num [hσ])
      _ = 2 := Real.rpow_one 2
  have hkey : x * x ^ σ = h * x ^ (σ + 3 / 50) := by
    rw [hh, ← Real.rpow_add hx0, ← Real.rpow_one_add' hx0.le (by norm_num [hσ])]
    congr 1; ring
  have hxe : x ^ (σ + 3 / 50) ≤ x ^ (19 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num [hσ])
  -- `log (2x) (h + 1) ≤ 2 h log (2 x) ≤ 2 x^{47/50} (1 + 100 x^{1/100}) ≤ 202 x^{19/20}`
  have hlogx : Real.log (2 * x) ≤ 1 + 100 * x ^ (1 / 100 : ℝ) := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have := log_le_rpow hx0.le
    have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hx1 : 1 ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hhx' : h * x ^ (1 / 100 : ℝ) ≤ x ^ (19 / 20 : ℝ) := by
    rw [hh, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hE : Real.log (2 * x) * (h + 1) ≤ 202 * x ^ (19 / 20 : ℝ) := by
    have h1 : Real.log (2 * x) * (h + 1) ≤ (1 + 100 * x ^ (1 / 100 : ℝ)) * (2 * h) := by
      gcongr; linarith
    have : h ≤ h * x ^ (1 / 100 : ℝ) := le_mul_of_one_le_right hh0.le hx1
    nlinarith
  have hS := hun
  rw [show Real.log (2 * x) * (h * (h + 1)) = h * (Real.log (2 * x) * (h + 1)) by ring] at hS
  have hmain : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (↗ξ * ↗Λ) n‖ ≤
      h * ((16 * K + 1000) * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := by
    have hlogm : 0 ≤ Real.log (m + 2) := by linarith
    have hX : 0 ≤ x ^ (19 / 20 : ℝ) := by positivity
    have hA : 4 * x * (K * (2 * x) ^ σ * Real.log (m + 2)) ≤
        h * (8 * K * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := by
      calc 4 * x * (K * (2 * x) ^ σ * Real.log (m + 2))
          ≤ 4 * x * (K * (2 * x ^ σ) * Real.log (m + 2)) := by gcongr
        _ = 8 * K * Real.log (m + 2) * (x * x ^ σ) := by ring
        _ = 8 * K * Real.log (m + 2) * (h * x ^ (σ + 3 / 50)) := by rw [hkey]
        _ ≤ 8 * K * Real.log (m + 2) * (h * x ^ (19 / 20 : ℝ)) := by gcongr
        _ = _ := by ring
    have hB : h * (Real.log (2 * x) * (h + 1)) ≤
        h * (404 * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hh0.le
      nlinarith
    have hC : h * (8 * K * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) +
        h * (404 * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) ≤
        h * ((16 * K + 1000) * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hh0.le
      have : 0 ≤ x ^ (19 / 20 : ℝ) * Real.log (m + 2) := mul_nonneg hX hlogm
      nlinarith
    calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (↗ξ * ↗Λ) n‖
        ≤ ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) (x + h) -
            (x : ℂ) * Riesz.rieszSum (↗ξ * ↗Λ) x‖ + h * (Real.log (2 * x) * (h + 1)) := hS
      _ ≤ 4 * x * (K * (2 * x) ^ σ * Real.log (m + 2)) +
            h * (404 * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := add_le_add hdiff hB
      _ ≤ h * (8 * K * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) +
            h * (404 * x ^ (19 / 20 : ℝ) * Real.log (m + 2)) := by linarith
      _ ≤ _ := hC
  have := le_of_mul_le_mul_left hmain hh0
  linarith

/-- **Prime sums.** `‖∑_{p ≤ x} ξ(p) log p‖ ≤ C x^{19/20} log (m + 2)` for every nonprincipal
`ξ` modulo `m` and every `x ≥ 1`. -/
theorem prime_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (ξ : DirichletCharacter ℂ m), ξ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (ξ p : ℂ) * Real.log p‖ ≤
          C * x ^ (19 / 20 : ℝ) * Real.log (m + 2) := by
  obtain ⟨C, hC, hCb⟩ := vonMangoldt_sum_bound
  refine ⟨C + 800, by positivity, ?_⟩
  intro m _ ξ hξ x hx
  have hx0 : 0 < x := by linarith
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hL : (1 / 2 : ℝ) ≤ Real.log (m + 2) := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log (m + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set s := Finset.Ioc 0 ⌊x⌋₊
  have hsplit := Finset.sum_filter_add_sum_filter_not s Nat.Prime (fun n => (↗ξ * ↗Λ) n)
  have hprime : ∑ p ∈ s with p.Prime, (ξ p : ℂ) * Real.log p =
      ∑ n ∈ s with n.Prime, (↗ξ * ↗Λ) n := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' := (Finset.mem_filter.mp hp).2
    simp [ArithmeticFunction.vonMangoldt_apply_prime hp']
  have hrest : ‖∑ n ∈ s with ¬ n.Prime, (↗ξ * ↗Λ) n‖ ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have hψ : Chebyshev.psi x = ∑ n ∈ s with n.Prime, Λ n + ∑ n ∈ s with ¬ n.Prime, Λ n := by
      rw [Finset.sum_filter_add_sum_filter_not]; rfl
    have hθ : Chebyshev.theta x = ∑ n ∈ s with n.Prime, Λ n := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm
    rw [hψ, hθ, add_sub_cancel_left]
    calc _ ≤ ∑ n ∈ s with ¬ n.Prime, ‖(↗ξ * ↗Λ) n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ s with ¬ n.Prime, Λ n := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
            (DirichletCharacter.norm_le_one ξ n)
  have hpt := Chebyshev.psi_sub_theta_le hx
  have hsq : 2 * √x * Real.log x ≤ 400 * x ^ (19 / 20 : ℝ) := by
    have h1 := log_le_rpow hx0.le
    have h2 : √x * x ^ (1 / 100 : ℝ) ≤ x ^ (19 / 20 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have h3 : 0 ≤ √x := Real.sqrt_nonneg x
    calc 2 * √x * Real.log x = 2 * (√x * Real.log x) := by ring
      _ ≤ 2 * (√x * (100 * x ^ (1 / 100 : ℝ))) := by gcongr
      _ = 200 * (√x * x ^ (1 / 100 : ℝ)) := by ring
      _ ≤ 200 * x ^ (19 / 20 : ℝ) := by gcongr
      _ ≤ 400 * x ^ (19 / 20 : ℝ) := by
          have : 0 ≤ x ^ (19 / 20 : ℝ) := by positivity
          linarith
  have hmain := hCb m ξ hξ x hx
  rw [hprime]
  have hX : 0 ≤ x ^ (19 / 20 : ℝ) := by positivity
  calc ‖∑ n ∈ s with n.Prime, (↗ξ * ↗Λ) n‖
      = ‖∑ n ∈ s, (↗ξ * ↗Λ) n - ∑ n ∈ s with ¬ n.Prime, (↗ξ * ↗Λ) n‖ := by
        rw [← hsplit, add_sub_cancel_right]
    _ ≤ ‖∑ n ∈ s, (↗ξ * ↗Λ) n‖ + ‖∑ n ∈ s with ¬ n.Prime, (↗ξ * ↗Λ) n‖ := norm_sub_le _ _
    _ ≤ C * x ^ (19 / 20 : ℝ) * Real.log (m + 2) + 400 * x ^ (19 / 20 : ℝ) := by
        linarith
    _ ≤ (C + 800) * x ^ (19 / 20 : ℝ) * Real.log (m + 2) := by nlinarith

end Vinogradov.PV
