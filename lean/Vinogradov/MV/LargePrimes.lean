/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

The large primes: for `m` in a block `(A, A + U]` and `p` prime in `(P, X]`, the bilinear bound
and the prime-pair bound give `‖∑_p log p f(p) ∑_m f(m) e(pmα)‖² ≤ U log²(X+1) W`, where
`W = ∑_{p, p'} wt_U((p - p')α)` is bounded through `pairs_le` and `sum_G_pow_four_le`.
-/
import Vinogradov.MV.GMoment
import Vinogradov.MV.SmallPrimes

noncomputable section

open Finset Complex Vinogradov.PV
open scoped Finset

namespace Vinogradov.MV

/-- **The pair sum.** -/
theorem pair_wt_le (V : Finset ℕ) (X : ℕ) (hV : ∀ v ∈ V, v ≤ X) {U : ℝ} (hU : 0 < U) (α : ℝ) :
    ∑ a ∈ V, ∑ b ∈ V, wt U (((a : ℝ) - b) * α) ≤
      #V * U + 2 * ∑ h ∈ Icc 1 X, wt U (h * α) * #{a ∈ V | a + h ∈ V} := by
  set F : ℕ → ℕ → ℝ := fun a b => wt U (((a : ℝ) - b) * α) with hF
  have hsymm : ∀ a b, F a b = F b a := by
    intro a b; simp only [hF]; rw [← wt_neg]; ring_nf
  have hsplit : ∀ a b, F a b = (if b < a then F a b else 0) + (if b = a then F a b else 0) +
      (if a < b then F a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.mpr h.le]
  -- the `a < b` part, row by row
  have hrow : ∀ a ∈ V, ∑ b ∈ V, (if a < b then F a b else 0) =
      ∑ h ∈ Icc 1 X, (if a + h ∈ V then wt U (h * α) else 0) := by
    intro a _
    rw [← sum_filter, ← sum_filter]
    apply sum_nbij' (fun b => b - a) (fun h => a + h)
    · intro b hb
      simp only [mem_filter] at hb ⊢
      have := hV b hb.1
      rw [mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show a + (b - a) = b by omega]; exact hb.1
    · intro h hh
      simp only [mem_filter, mem_Icc] at hh ⊢
      exact ⟨hh.2, by omega⟩
    · intro b hb
      simp only [mem_filter] at hb
      omega
    · intro h _; omega
    · intro b hb
      simp only [mem_filter] at hb
      simp only [hF]
      rw [Nat.cast_sub hb.2.le, ← wt_neg]; ring_nf
  have hA : ∑ a ∈ V, ∑ b ∈ V, (if a < b then F a b else 0) =
      ∑ h ∈ Icc 1 X, wt U (h * α) * #{a ∈ V | a + h ∈ V} := by
    rw [sum_congr rfl hrow, sum_comm]
    apply sum_congr rfl; intro h _
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∑ a ∈ V, ∑ b ∈ V, (if b < a then F a b else 0) =
      ∑ a ∈ V, ∑ b ∈ V, (if a < b then F a b else 0) := by
    rw [sum_comm]
    apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
    rw [hsymm]
  have hC : ∑ a ∈ V, ∑ b ∈ V, (if b = a then F a b else 0) ≤ #V * U := by
    calc _ = ∑ a ∈ V, F a a := by
          apply sum_congr rfl; intro a ha; rw [sum_ite_eq' V a (F a)]; simp [ha]
      _ ≤ ∑ _a ∈ V, U := sum_le_sum fun a _ => wt_le hU _
      _ = #V * U := by rw [sum_const, nsmul_eq_mul]
  calc ∑ a ∈ V, ∑ b ∈ V, F a b
      = ∑ a ∈ V, ∑ b ∈ V, (if b < a then F a b else 0) +
        ∑ a ∈ V, ∑ b ∈ V, (if b = a then F a b else 0) +
        ∑ a ∈ V, ∑ b ∈ V, (if a < b then F a b else 0) := by
        rw [← sum_add_distrib, ← sum_add_distrib]
        apply sum_congr rfl; intro a _
        rw [← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun b _ => hsplit a b
    _ ≤ _ := by rw [hB, hA]; linarith

/-- **The pair count.** For `V` a set of odd primes in `[1, X]`, the number of `a ∈ V` with
`a + h ∈ V` is at most the prime-pair bound for `n < X + 1`. -/
theorem card_pairs_le (V : Finset ℕ) (X h : ℕ) (hV : ∀ v ∈ V, v.Prime ∧ 2 < v ∧ v ≤ X)
    (hX : 1 ≤ X) (hh : 0 < h) :
    (#{a ∈ V | a + h ∈ V} : ℝ) ≤
      400 * G h ^ 2 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 +
        3 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) := by
  have hX1 : (0 : ℝ) ≤ (X : ℝ) + 1 := by positivity
  have hrhs : 0 ≤ 400 * G h ^ 2 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 +
      3 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) := by positivity
  by_cases h2 : 2 ∣ h
  · have hsub : {a ∈ V | a + h ∈ V} ⊆
        {n ∈ Finset.range (X + 1) | n.Prime ∧ (n + h).Prime} := by
      intro a ha
      rw [mem_filter] at ha
      rw [mem_filter, mem_range]
      have h1 := hV a ha.1
      have h2 := hV (a + h) ha.2
      exact ⟨by omega, h1.1, h2.1⟩
    have hp := pairs_le (X + 1) h (by omega) h2 hh.ne'
    push_cast at hp
    calc (#{a ∈ V | a + h ∈ V} : ℝ)
        ≤ (#{n ∈ Finset.range (X + 1) | n.Prime ∧ (n + h).Prime} : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ _ := hp
  · have hempty : {a ∈ V | a + h ∈ V} = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro a ha hah
      have h1 := hV a ha
      have h3 := hV (a + h) hah
      obtain ⟨k, hk⟩ := h1.1.odd_of_ne_two (by omega)
      obtain ⟨k', hk'⟩ := h3.1.odd_of_ne_two (by omega)
      exact h2 ⟨k' - k, by omega⟩
    rw [hempty, card_empty, Nat.cast_zero]
    exact hrhs

theorem sqrt_exp_thirty : Real.sqrt (Real.exp 30) = Real.exp 15 := by
  rw [show (30 : ℝ) = 15 + 15 by norm_num, Real.exp_add, ← sq, Real.sqrt_sq (Real.exp_pos _).le]

/-- **The pair sum `W`.** -/
theorem W_le {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den)
    (V : Finset ℕ) (X : ℕ) (hV : ∀ v ∈ V, v.Prime ∧ 2 < v ∧ v ≤ X) (hX : 1 ≤ X)
    {U : ℝ} (hU : 0 < U) :
    ∑ p ∈ V, ∑ p' ∈ V, wt U (((p : ℝ) - p') * α) ≤
      X * U + 800 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 *
        (Real.exp 15 * Real.sqrt X *
          Real.sqrt ((4 * X / a.den + 1) * (20 * a.den * U + 3 * U ^ 2))) +
        6 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) * X * U := by
  set r : ℕ := a.den with hrdef
  set Q : ℝ := (4 * X / r + 1) * (20 * r * U + 3 * U ^ 2) with hQ
  set c1 : ℝ := 400 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 with hc1
  set c2 : ℝ := 3 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hwt0 : ∀ θ, 0 ≤ wt U θ := wt_nonneg hU.le
  have hV1 : (#V : ℝ) ≤ X := by
    have : V ⊆ Icc 1 X := by
      intro v hv; have := hV v hv; rw [mem_Icc]; exact ⟨this.1.one_lt.le, this.2.2⟩
    have := card_le_card this
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hpair := pair_wt_le V X (fun v hv => (hV v hv).2.2) hU α
  -- the weighted pair counts
  have hcount : ∑ h ∈ Icc 1 X, wt U (h * α) * #{a ∈ V | a + h ∈ V} ≤
      c1 * ∑ h ∈ Icc 1 X, G h ^ 2 * wt U (h * α) + c2 * ∑ h ∈ Icc 1 X, wt U (h * α) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro h hh
    rw [mem_Icc] at hh
    have hc := card_pairs_le V X h hV hX (by omega)
    have := mul_le_mul_of_nonneg_left hc (hwt0 (h * α))
    calc wt U (h * α) * #{a ∈ V | a + h ∈ V}
        ≤ wt U (h * α) * (400 * G h ^ 2 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 +
          3 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ)) := this
      _ = c1 * (G h ^ 2 * wt U (h * α)) + c2 * wt U (h * α) := by
          rw [hc1, hc2]; ring
  -- Cauchy–Schwarz for the `G²` sum
  have hCS : ∑ h ∈ Icc 1 X, G h ^ 2 * wt U (h * α) ≤
      Real.exp 15 * Real.sqrt X * Real.sqrt Q := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt (Icc 1 X) (fun h => G h ^ 2) (fun h => wt U (h * α))
    have h2 : Real.sqrt (∑ h ∈ Icc 1 X, (G h ^ 2) ^ 2) ≤ Real.exp 15 * Real.sqrt X := by
      have : ∑ h ∈ Icc 1 X, (G h ^ 2) ^ 2 = ∑ h ∈ Icc 1 X, G h ^ 4 := by
        apply sum_congr rfl; intro h _; ring
      rw [this]
      calc _ ≤ Real.sqrt (Real.exp 30 * X) := Real.sqrt_le_sqrt (sum_G_pow_four_le X)
        _ = _ := by rw [Real.sqrt_mul (Real.exp_pos _).le, sqrt_exp_thirty]
    have h3 : Real.sqrt (∑ h ∈ Icc 1 X, wt U (h * α) ^ 2) ≤ Real.sqrt Q :=
      Real.sqrt_le_sqrt (sum_wt_sq_le hα hr X hU)
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul h2 h3 (Real.sqrt_nonneg _) (by positivity)
  have hsw : ∑ h ∈ Icc 1 X, wt U (h * α) ≤ X * U := by
    calc _ ≤ ∑ _h ∈ Icc 1 X, U := sum_le_sum fun h _ => wt_le hU _
      _ = X * U := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hXU : (#V : ℝ) * U ≤ X * U := mul_le_mul_of_nonneg_right hV1 hU.le
  have e1 := mul_le_mul_of_nonneg_left hCS hc10
  have e2 := mul_le_mul_of_nonneg_left hsw hc20
  calc _ ≤ _ := hpair
    _ ≤ X * U + 2 * (c1 * (Real.exp 15 * Real.sqrt X * Real.sqrt Q) + c2 * (X * U)) := by
        linarith
    _ = _ := by rw [hc1, hc2]; ring

/-- **One block of large primes**, `m ∈ (A, A + U]`, `p ∈ (P, N/(A+1)]`. -/
theorem block_raw (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} {a : ℚ}
    (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (N P A U : ℕ) (hP : 2 ≤ P)
    (hU : 0 < U) (hX : 1 ≤ N / (A + 1)) :
    ‖∑ p ∈ Ioc P N with p.Prime, (Real.log p : ℂ) * f p *
        ∑ m ∈ Ioc A (A + U), (if p * m ≤ N then f m * e (p * m * α) else 0)‖ ≤
      Real.sqrt (U * Real.log (((N / (A + 1) : ℕ) : ℝ) + 1) ^ 2 *
        (((N / (A + 1) : ℕ) : ℝ) * U + 800 * (((N / (A + 1) : ℕ) : ℝ) + 1) /
          Real.log (((N / (A + 1) : ℕ) : ℝ) + 1) ^ 2 *
          (Real.exp 15 * Real.sqrt ((N / (A + 1) : ℕ) : ℝ) *
            Real.sqrt ((4 * ((N / (A + 1) : ℕ) : ℝ) / a.den + 1) *
              (20 * a.den * (U : ℝ) + 3 * (U : ℝ) ^ 2))) +
          6 * (((N / (A + 1) : ℕ) : ℝ) + 1) ^ (3 / 5 : ℝ) * ((N / (A + 1) : ℕ) : ℝ) * U)) := by
  set X : ℕ := N / (A + 1) with hXdef
  set V : Finset ℕ := (Ioc P X).filter Nat.Prime with hVdef
  set L' : ℝ := Real.log ((X : ℝ) + 1) with hL'
  have hL'0 : 0 ≤ L' := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hXN : X ≤ N := Nat.div_le_self N (A + 1)
  have hVsub : V ⊆ (Ioc P N).filter Nat.Prime := by
    intro p hp
    simp only [hVdef, mem_filter, mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hXN⟩, hp.2⟩
  have hNlt : N < (X + 1) * (A + 1) := by
    have := Nat.lt_div_mul_add (a := N) (show 0 < A + 1 by omega)
    rw [hXdef]; nlinarith
  have hzero : ∀ p ∈ (Ioc P N).filter Nat.Prime, p ∉ V →
      (Real.log p : ℂ) * f p *
        ∑ m ∈ Ioc A (A + U), (if p * m ≤ N then f m * e (p * m * α) else 0) = 0 := by
    intro p hp hpV
    simp only [hVdef, mem_filter, mem_Ioc] at hp hpV
    have hpX : X < p := by
      by_contra h; push Not at h; exact hpV ⟨⟨hp.1.1, h⟩, hp.2⟩
    rw [sum_eq_zero, mul_zero]
    intro m hm
    rw [mem_Ioc] at hm
    have : (X + 1) * (A + 1) ≤ p * m := Nat.mul_le_mul (by omega) (by omega)
    exact if_neg (by omega)
  rw [← sum_subset hVsub hzero]
  -- swap the sums
  set b : ℕ → ℂ := fun p => (Real.log p : ℂ) * f p with hb
  set B : ℕ → ℂ := fun m => ∑ p ∈ V, (if m * p ≤ N then b p * e (m * p * α) else 0) with hB
  have hswap : ∑ p ∈ V, (Real.log p : ℂ) * f p *
      ∑ m ∈ Ioc A (A + U), (if p * m ≤ N then f m * e (p * m * α) else 0) =
      ∑ m ∈ Ioc A (A + U), f m * B m := by
    simp_rw [hB, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro m _; apply sum_congr rfl; intro p _
    rw [mul_comm m p]
    split_ifs
    · simp only [hb]; rw [mul_comm (m : ℝ) (p : ℝ)]; ring
    · simp
  rw [hswap]
  -- norms and Cauchy–Schwarz over `m`
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have h1 : ‖∑ m ∈ Ioc A (A + U), f m * B m‖ ≤ ∑ m ∈ Ioc A (A + U), 1 * ‖B m‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hfb m) (norm_nonneg _)
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Ioc A (A + U)) (fun _ => (1 : ℝ)) (fun m => ‖B m‖)
  have hone : ∑ m ∈ Ioc A (A + U), ((fun _ => (1 : ℝ)) m) ^ 2 = U := by
    simp only [one_pow, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    rw [Nat.add_sub_cancel_left]
  rw [hone] at hCS
  -- the bilinear bound
  have hbil := bilinear_wt A (A + U) N hU' (by push_cast; linarith) V
    (fun v hv => (mem_filter.mp hv).2.pos) b α
  have hV : ∀ v ∈ V, v.Prime ∧ 2 < v ∧ v ≤ X := by
    intro v hv
    simp only [hVdef, mem_filter, mem_Ioc] at hv
    exact ⟨hv.2, by omega, hv.1.2⟩
  have hbn : ∀ p ∈ V, ‖b p‖ ≤ L' := by
    intro p hp
    have hpX := (hV p hp).2.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hV p hp).1.pos
    simp only [hb]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg p)]
    calc Real.log p * ‖f p‖ ≤ Real.log p * 1 :=
          mul_le_mul_of_nonneg_left (hfb p) (Real.log_natCast_nonneg p)
      _ = Real.log p := mul_one _
      _ ≤ L' := by
          rw [hL']; apply Real.log_le_log hp0
          have : (p : ℝ) ≤ X := by exact_mod_cast hpX
          linarith
  have hsum : ∑ v ∈ V, ∑ v' ∈ V, ‖b v‖ * ‖b v'‖ * wt U (((v : ℝ) - v') * α) ≤
      L' ^ 2 * ∑ v ∈ V, ∑ v' ∈ V, wt U (((v : ℝ) - v') * α) := by
    rw [mul_sum]
    apply sum_le_sum; intro v hv
    rw [mul_sum]
    apply sum_le_sum; intro v' hv'
    have h := mul_le_mul (hbn v hv) (hbn v' hv') (norm_nonneg _) hL'0
    have := mul_le_mul_of_nonneg_right h (wt_nonneg hU'.le (((v : ℝ) - v') * α))
    linarith
  have hW := W_le hα hr V X hV hX hU'
  have hBsq : ∑ m ∈ Ioc A (A + U), ‖B m‖ ^ 2 ≤ L' ^ 2 *
      ((X : ℝ) * U + 800 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 *
        (Real.exp 15 * Real.sqrt X *
          Real.sqrt ((4 * X / a.den + 1) * (20 * a.den * (U : ℝ) + 3 * (U : ℝ) ^ 2))) +
        6 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) * X * U) := by
    calc _ ≤ _ := hbil
      _ ≤ _ := hsum
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (sq_nonneg _)
  calc _ ≤ _ := h1
    _ ≤ _ := hCS
    _ ≤ Real.sqrt U * Real.sqrt (L' ^ 2 *
      ((X : ℝ) * U + 800 * ((X : ℝ) + 1) / Real.log ((X : ℝ) + 1) ^ 2 *
        (Real.exp 15 * Real.sqrt X *
          Real.sqrt ((4 * X / a.den + 1) * (20 * a.den * (U : ℝ) + 3 * (U : ℝ) ^ 2))) +
        6 * ((X : ℝ) + 1) ^ (3 / 5 : ℝ) * X * U)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBsq) (Real.sqrt_nonneg _)
    _ = _ := by rw [← Real.sqrt_mul hU'.le]; congr 1; rw [hL']; ring

/-! ### Fourth roots -/

/-- The fourth root `√√x`. -/
def q4 (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem q4_nonneg (x : ℝ) : 0 ≤ q4 x := Real.sqrt_nonneg _

theorem q4_pow_four {x : ℝ} (hx : 0 ≤ x) : q4 x ^ 4 = x := by
  unfold q4
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hx]

theorem q4_mono {x y : ℝ} (h : x ≤ y) : q4 x ≤ q4 y :=
  Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem sqrt_le_of_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  (Real.sqrt_le_sqrt h).trans (Real.sqrt_sq hy).le

theorem q4_le_of_le_pow {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 4) : q4 x ≤ y := by
  unfold q4
  apply sqrt_le_of_le_sq hy
  apply sqrt_le_of_le_sq (sq_nonneg y)
  rw [← pow_mul]; exact h

theorem q4_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : q4 (x + y) ≤ q4 x + q4 y := by
  unfold q4
  calc Real.sqrt (Real.sqrt (x + y)) ≤ Real.sqrt (Real.sqrt x + Real.sqrt y) :=
        Real.sqrt_le_sqrt (sqrt_add_le' hx hy)
    _ ≤ _ := sqrt_add_le' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sqrt_eq_q4_sq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = q4 (x ^ 2) := by
  unfold q4; rw [Real.sqrt_sq hx]

theorem q4_eq_rpow {x : ℝ} (hx : 0 ≤ x) : q4 x = x ^ (1 / 4 : ℝ) := by
  unfold q4
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

theorem log_le_four_q4 {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 4 * q4 x := by
  have h := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 4 by norm_num)
  rw [← q4_eq_rpow hx] at h
  linarith

theorem one_le_q4 {x : ℝ} (hx : 1 ≤ x) : 1 ≤ q4 x := by
  unfold q4
  rw [Real.one_le_sqrt, Real.one_le_sqrt]; exact hx

theorem q4_le_sqrt {x : ℝ} (hx : 1 ≤ x) : q4 x ≤ Real.sqrt x := by
  unfold q4
  have h1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  apply sqrt_le_of_le_sq (by linarith)
  nlinarith

/-- **The main term of a block.** With `u = 15M`, `M = 16^i`, `xM ≤ n` and `R ≤ r ≤ n/R`,
`√(u (x+1) √x √((4x/r + 1)(20ru + 3u²))) ≤ 40 (n/2^i + 2n/R^{1/4} + 2^i n^{3/4})`. -/
theorem sqrtZ_le {n x r R : ℝ} (i : ℕ) (hx : 1 ≤ x) (hxM : x * 16 ^ i ≤ n) (hR : 0 < R)
    (hRr : R ≤ r) (hrn : r ≤ n / R) :
    Real.sqrt ((15 * 16 ^ i) * (x + 1) * Real.sqrt x *
      Real.sqrt ((4 * x / r + 1) * (20 * r * (15 * 16 ^ i) + 3 * (15 * 16 ^ i) ^ 2))) ≤
      40 * (n / 2 ^ i + 2 * (n / q4 R) + 2 ^ i * q4 n ^ 3) := by
  set M : ℝ := 16 ^ i with hMdef
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have h2M : ((2 : ℝ) ^ i) ^ 4 = M := by
    rw [hMdef, ← pow_mul, mul_comm, pow_mul]; norm_num
  set u : ℝ := 15 * M with hu
  have hu0 : 0 < u := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hR hRr
  have hn : 1 ≤ n := by nlinarith
  have hn0 : 0 ≤ n := by linarith
  set Q : ℝ := (4 * x / r + 1) * (20 * r * u + 3 * u ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set Z : ℝ := u * (x + 1) * Real.sqrt x * Real.sqrt Q with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hZ2 : Z ^ 2 = u ^ 2 * (x + 1) ^ 2 * x * Q := by
    rw [hZ, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hQ0]
  set w : ℝ := u * x with hw
  have hw0 : 0 ≤ w := by positivity
  have hw15 : w ≤ 15 * n := by rw [hw, hu]; nlinarith
  have hxn : x ≤ n / M := by rw [le_div_iff₀ (by positivity)]; exact hxM
  have h4 : Z ^ 2 ≤ 320 * w ^ 3 * x + 48 * w ^ 4 / r + 80 * r * w ^ 3 + 12 * u * w ^ 3 := by
    have hx1 : (x + 1) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    have e : 4 * u ^ 2 * x ^ 3 * Q =
        320 * w ^ 3 * x + 48 * w ^ 4 / r + 80 * r * w ^ 3 + 12 * u * w ^ 3 := by
      rw [hQ, hw]; field_simp; ring
    rw [hZ2, ← e]
    have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ u ^ 2)
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ x * Q)
    nlinarith
  have hw3 : w ^ 3 ≤ (15 * n) ^ 3 := pow_le_pow_left₀ hw0 hw15 3
  have hw4 : w ^ 4 ≤ (15 * n) ^ 4 := pow_le_pow_left₀ hw0 hw15 4
  have hT1 : 320 * w ^ 3 * x ≤ 320 * 15 ^ 3 * n ^ 4 / M := by
    have := mul_le_mul hw3 hxn (by linarith) (by positivity)
    calc 320 * w ^ 3 * x = 320 * (w ^ 3 * x) := by ring
      _ ≤ 320 * ((15 * n) ^ 3 * (n / M)) := by linarith
      _ = _ := by ring
  have hT2 : 48 * w ^ 4 / r ≤ 48 * 15 ^ 4 * n ^ 4 / R := by
    calc 48 * w ^ 4 / r ≤ 48 * (15 * n) ^ 4 / r := by gcongr
      _ ≤ 48 * (15 * n) ^ 4 / R := div_le_div_of_nonneg_left (by positivity) hR hRr
      _ = _ := by ring
  have hT3 : 80 * r * w ^ 3 ≤ 80 * 15 ^ 3 * n ^ 4 / R := by
    calc 80 * r * w ^ 3 ≤ 80 * (n / R) * (15 * n) ^ 3 := by gcongr
      _ = _ := by ring
  have hT4 : 12 * u * w ^ 3 ≤ 180 * 15 ^ 3 * M * n ^ 3 := by
    calc 12 * u * w ^ 3 ≤ 12 * u * (15 * n) ^ 3 := by gcongr
      _ = _ := by rw [hu]; ring
  have hq4R : 0 < q4 R := by
    unfold q4; apply Real.sqrt_pos.mpr; exact Real.sqrt_pos.mpr hR
  have hR4 : q4 R ^ 4 = R := q4_pow_four hR.le
  have hn4 : q4 n ^ 4 = n := q4_pow_four hn0
  have a1 : q4 (320 * 15 ^ 3 * n ^ 4 / M) ≤ 40 * (n / 2 ^ i) := by
    apply q4_le_of_le_pow (by positivity)
    rw [mul_pow, div_pow, h2M, ← mul_div_assoc]
    have c : (320 : ℝ) * 15 ^ 3 ≤ 40 ^ 4 := by norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right c (pow_nonneg hn0 4))
      (by positivity)
  have a2 : q4 (48 * 15 ^ 4 * n ^ 4 / R) ≤ 40 * (n / q4 R) := by
    apply q4_le_of_le_pow (by positivity)
    rw [mul_pow, div_pow, hR4, ← mul_div_assoc]
    have c : (48 : ℝ) * 15 ^ 4 ≤ 40 ^ 4 := by norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right c (pow_nonneg hn0 4)) hR.le
  have a3 : q4 (80 * 15 ^ 3 * n ^ 4 / R) ≤ 40 * (n / q4 R) := by
    apply q4_le_of_le_pow (by positivity)
    rw [mul_pow, div_pow, hR4, ← mul_div_assoc]
    have c : (80 : ℝ) * 15 ^ 3 ≤ 40 ^ 4 := by norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right c (pow_nonneg hn0 4)) hR.le
  have hq4n := q4_nonneg n
  have a4 : q4 (180 * 15 ^ 3 * M * n ^ 3) ≤ 40 * (2 ^ i * q4 n ^ 3) := by
    apply q4_le_of_le_pow (by positivity)
    have : (40 * (2 ^ i * q4 n ^ 3)) ^ 4 = 40 ^ 4 * M * n ^ 3 := by
      calc (40 * (2 ^ i * q4 n ^ 3)) ^ 4 = 40 ^ 4 * ((2 : ℝ) ^ i) ^ 4 * (q4 n ^ 4) ^ 3 := by ring
        _ = _ := by rw [h2M, hn4]
    rw [this]
    have c : (180 : ℝ) * 15 ^ 3 ≤ 40 ^ 4 := by norm_num
    have := mul_le_mul_of_nonneg_right c
      (mul_nonneg (by linarith : (0 : ℝ) ≤ M) (pow_nonneg hn0 3))
    linarith
  have b0 : 0 ≤ 320 * 15 ^ 3 * n ^ 4 / M := by positivity
  have b1 : 0 ≤ 48 * 15 ^ 4 * n ^ 4 / R := by positivity
  have b2 : 0 ≤ 80 * 15 ^ 3 * n ^ 4 / R := by positivity
  have b3 : 0 ≤ 180 * 15 ^ 3 * M * n ^ 3 := by positivity
  rw [sqrt_eq_q4_sq hZ0]
  calc q4 (Z ^ 2) ≤ q4 (320 * 15 ^ 3 * n ^ 4 / M + 48 * 15 ^ 4 * n ^ 4 / R +
        80 * 15 ^ 3 * n ^ 4 / R + 180 * 15 ^ 3 * M * n ^ 3) := by
        apply q4_mono; linarith
    _ ≤ q4 (320 * 15 ^ 3 * n ^ 4 / M) + q4 (48 * 15 ^ 4 * n ^ 4 / R) +
        q4 (80 * 15 ^ 3 * n ^ 4 / R) + q4 (180 * 15 ^ 3 * M * n ^ 3) := by
        refine (q4_add_le (by positivity) b3).trans (add_le_add ?_ le_rfl)
        refine (q4_add_le (by positivity) b2).trans (add_le_add ?_ le_rfl)
        exact q4_add_le b0 b1
    _ ≤ 40 * (n / 2 ^ i) + 40 * (n / q4 R) + 40 * (n / q4 R) + 40 * (2 ^ i * q4 n ^ 3) :=
        add_le_add (add_le_add (add_le_add a1 a2) a3) a4
    _ = _ := by ring

/-- The constant of `block_bound`. -/
def Kb : ℝ := 80 * Real.sqrt (800 * Real.exp 15) + 52

theorem Kb_pos : 0 < Kb := by unfold Kb; positivity

/-- **One 16-adic block of large primes**, `m ∈ [16^i, 16^{i+1})`. -/
theorem block_bound (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} {a : ℚ}
    (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (N P i : ℕ) (hP : 2 ≤ P) {R : ℝ}
    (hR : 0 < R) (hRr : R ≤ a.den) (hrN : (a.den : ℝ) ≤ N / R) :
    ‖∑ p ∈ Ioc P N with p.Prime, (Real.log p : ℂ) * f p *
        ∑ m ∈ Ioc (16 ^ i - 1) (16 ^ i - 1 + 15 * 16 ^ i),
          (if p * m ≤ N then f m * e (p * m * α) else 0)‖ ≤
      Kb * (N / 2 ^ i + N / q4 R + 2 ^ i * q4 N ^ 3 +
        4 ^ i * Real.log ((N : ℝ) + 1) * Real.sqrt (N * (2 * N) ^ (3 / 5 : ℝ))) := by
  have h16 : 1 ≤ 16 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have hA1 : 16 ^ i - 1 + 1 = 16 ^ i := Nat.sub_add_cancel h16
  set n : ℝ := (N : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg N
  have hq4n := q4_nonneg n
  have hq4R := q4_nonneg R
  have hrhs0 : 0 ≤ Kb * (n / 2 ^ i + n / q4 R + 2 ^ i * q4 n ^ 3 +
      4 ^ i * Real.log (n + 1) * Real.sqrt (n * (2 * n) ^ (3 / 5 : ℝ))) := by
    have := Kb_pos
    have := Real.log_nonneg (show (1 : ℝ) ≤ n + 1 by linarith)
    positivity
  by_cases hX : 1 ≤ N / 16 ^ i
  swap
  · -- no `p` survives
    push Not at hX
    have hN : N < 16 ^ i := by
      rcases Nat.lt_one_iff.mp hX with h
      exact (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    rw [sum_eq_zero, norm_zero]
    · exact hrhs0
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    rw [sum_eq_zero, mul_zero]
    intro m hm
    rw [mem_Ioc] at hm
    have : m ≤ p * m := Nat.le_mul_of_pos_left m (by omega)
    exact if_neg (by omega)
  have hraw := block_raw f hfb hα hr N P (16 ^ i - 1) (15 * 16 ^ i) hP (by positivity)
    (by rw [hA1]; exact hX)
  rw [hA1] at hraw
  refine hraw.trans ?_
  set X : ℕ := N / 16 ^ i with hXdef
  set x : ℝ := (X : ℝ) with hx
  set r : ℕ := a.den with hrdef
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hX
  have hxM : x * 16 ^ i ≤ n := by
    have := Nat.div_mul_le_self N (16 ^ i)
    rw [hx, hn]; exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ 16 ^ i := one_le_pow₀ (by norm_num)
  have hxn : x ≤ n := by nlinarith
  have hn1 : 1 ≤ n := by linarith
  set L' : ℝ := Real.log (x + 1) with hL'
  set Lg : ℝ := Real.log (n + 1) with hLg
  have hL'0 : 0 < L' := Real.log_pos (by linarith)
  have hLL : L' ≤ Lg := Real.log_le_log (by linarith) (by linarith)
  set E : ℝ := Real.exp 15 with hE
  set Q : ℝ := (4 * x / r + 1) * (20 * r * ((15 * 16 ^ i : ℕ) : ℝ) +
    3 * ((15 * 16 ^ i : ℕ) : ℝ) ^ 2) with hQ
  set u : ℝ := ((15 * 16 ^ i : ℕ) : ℝ) with hu
  have hu' : u = 15 * 16 ^ i := by rw [hu]; push_cast; ring
  have hu0 : 0 ≤ u := by rw [hu']; positivity
  set W : ℝ := (2 * n) ^ (3 / 5 : ℝ) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow (by linarith) (by norm_num)
  have hxW : (x + 1) ^ (3 / 5 : ℝ) ≤ W :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hxW0 : 0 ≤ (x + 1) ^ (3 / 5 : ℝ) := by positivity
  -- the three terms
  set A1 : ℝ := u ^ 2 * L' ^ 2 * x with hA1d
  set A2 : ℝ := 800 * E * (u * (x + 1) * Real.sqrt x * Real.sqrt Q) with hA2d
  set A3 : ℝ := 6 * u ^ 2 * L' ^ 2 * (x + 1) ^ (3 / 5 : ℝ) * x with hA3d
  have hQ0 : 0 ≤ Q := by positivity
  have hid : u * L' ^ 2 * (x * u + 800 * (x + 1) / L' ^ 2 *
      (E * Real.sqrt x * Real.sqrt Q) + 6 * (x + 1) ^ (3 / 5 : ℝ) * x * u) = A1 + A2 + A3 := by
    rw [hA1d, hA2d, hA3d]; field_simp
  rw [hid]
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  have hsplit : Real.sqrt (A1 + A2 + A3) ≤ Real.sqrt A1 + Real.sqrt A2 + Real.sqrt A3 :=
    (sqrt_add_le' (by positivity) hA30).trans (add_le_add (sqrt_add_le' hA10 hA20) le_rfl)
  -- `u² x ≤ 225 16^i n`
  have hux : u ^ 2 * x ≤ 225 * 16 ^ i * n := by
    rw [hu']
    calc (15 * (16 : ℝ) ^ i) ^ 2 * x = 225 * 16 ^ i * (x * 16 ^ i) := by ring
      _ ≤ 225 * 16 ^ i * n := mul_le_mul_of_nonneg_left hxM (by positivity)
  have hL2 : L' ^ 2 ≤ Lg ^ 2 := pow_le_pow_left₀ hL'0.le hLL 2
  set T : ℝ := 4 ^ i * Lg * Real.sqrt (n * W) with hT
  have hLg0 : 0 ≤ Lg := hL'0.le.trans hLL
  have hT0 : 0 ≤ T := by positivity
  have hTsq : T ^ 2 = 16 ^ i * Lg ^ 2 * (n * W) := by
    rw [hT, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm i 2, pow_mul]
    norm_num
  have hP0 : 0 ≤ 16 ^ i * n := by positivity
  have s1 : Real.sqrt A1 ≤ 15 * T := by
    apply sqrt_le_of_le_sq (by positivity)
    rw [mul_pow, hTsq, hA1d]
    have e1 : u ^ 2 * L' ^ 2 * x = (u ^ 2 * x) * L' ^ 2 := by ring
    rw [e1]
    have h1 := mul_le_mul hux hL2 (sq_nonneg _) (by positivity)
    have h2 : 225 * 16 ^ i * n * Lg ^ 2 ≤ 225 * 16 ^ i * n * Lg ^ 2 * W :=
      le_mul_of_one_le_right (by positivity) hW1
    calc _ ≤ 225 * 16 ^ i * n * Lg ^ 2 := h1
      _ ≤ _ := h2
      _ = _ := by ring
  have s3 : Real.sqrt A3 ≤ 37 * T := by
    apply sqrt_le_of_le_sq (by positivity)
    rw [mul_pow, hTsq, hA3d]
    have e1 : 6 * u ^ 2 * L' ^ 2 * (x + 1) ^ (3 / 5 : ℝ) * x =
        6 * ((u ^ 2 * x) * L' ^ 2) * (x + 1) ^ (3 / 5 : ℝ) := by ring
    rw [e1]
    have h1 := mul_le_mul hux hL2 (sq_nonneg _) (by positivity)
    have h2 := mul_le_mul h1 hxW hxW0 (by positivity)
    have h3 : 0 ≤ 225 * 16 ^ i * n * Lg ^ 2 * W := by positivity
    calc _ ≤ 6 * (225 * 16 ^ i * n * Lg ^ 2 * W) := by linarith
      _ ≤ 37 ^ 2 * (225 * 16 ^ i * n * Lg ^ 2 * W) / 225 := by linarith
      _ = _ := by ring
  have s2 : Real.sqrt A2 ≤ Real.sqrt (800 * E) * (40 * (n / 2 ^ i + 2 * (n / q4 R) +
      2 ^ i * q4 n ^ 3)) := by
    rw [hA2d, Real.sqrt_mul (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have hZ := sqrtZ_le (n := n) (x := x) (r := (r : ℝ)) i hx1 hxM hR hRr hrN
    have e : u * (x + 1) * Real.sqrt x * Real.sqrt Q = (15 * 16 ^ i) * (x + 1) * Real.sqrt x *
        Real.sqrt ((4 * x / r + 1) * (20 * r * (15 * 16 ^ i) + 3 * (15 * 16 ^ i) ^ 2)) := by
      rw [hQ, hu']
    rw [e]; exact hZ
  set sE : ℝ := Real.sqrt (800 * E) with hsE
  have hsE0 : 0 ≤ sE := Real.sqrt_nonneg _
  have ha : 0 ≤ n / 2 ^ i := by positivity
  have hb : 0 ≤ n / q4 R := by positivity
  have hc : 0 ≤ 2 ^ i * q4 n ^ 3 := by positivity
  have hKb : Kb = 80 * sE + 52 := rfl
  rw [hKb]
  have key : 15 * T + sE * (40 * (n / 2 ^ i + 2 * (n / q4 R) + 2 ^ i * q4 n ^ 3)) + 37 * T ≤
      (80 * sE + 52) * (n / 2 ^ i + n / q4 R + 2 ^ i * q4 n ^ 3 + T) := by
    rw [← sub_nonneg]
    have e : (80 * sE + 52) * (n / 2 ^ i + n / q4 R + 2 ^ i * q4 n ^ 3 + T) -
        (15 * T + sE * (40 * (n / 2 ^ i + 2 * (n / q4 R) + 2 ^ i * q4 n ^ 3)) + 37 * T) =
        40 * (sE * (n / 2 ^ i)) + 40 * (sE * (2 ^ i * q4 n ^ 3)) + 80 * (sE * T) +
          52 * (n / 2 ^ i) + 52 * (n / q4 R) + 52 * (2 ^ i * q4 n ^ 3) := by ring
    rw [e]
    have := mul_nonneg hsE0 ha
    have := mul_nonneg hsE0 hc
    have := mul_nonneg hsE0 hT0
    linarith
  calc _ ≤ _ := hsplit
    _ ≤ _ := add_le_add (add_le_add s1 s2) s3
    _ ≤ _ := key
    _ = _ := by rw [hT]

end Vinogradov.MV
