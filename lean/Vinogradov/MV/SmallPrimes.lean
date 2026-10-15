import Vinogradov.MV.Reduction

/-!
# The small primes

For `p ≤ 2^J`, split `p` into dyadic blocks `(U, 2U]`, `U = 2^j`, and apply Cauchy–Schwarz over
`p` and the bilinear bound over `x ∈ (U, 2U]`:
`‖∑_{U < p ≤ 2U} log p f(p) ∑_{m ≤ N/p} f(m) e(pmα)‖
  ≤ (j + 1) (√(7NU) + N √(24/r) + N √((32 + 64 j)/U) + √((8 + 16 j) N r))`.
-/

namespace Vinogradov.MV

open Finset Complex Vinogradov.PV

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- `∑_{m ≤ N/p} g(m) = ∑_{m ≤ H} [pm ≤ N] g(m)` when `N/p ≤ H`. -/
theorem sum_Ioc_div_eq (N p H : ℕ) (hp : 0 < p) (hH : N / p ≤ H) (g : ℕ → ℂ) :
    ∑ m ∈ Ioc 0 (N / p), g m = ∑ m ∈ Ioc 0 H, (if p * m ≤ N then g m else 0) := by
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [mem_Ioc, mem_filter]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨⟨h0, h1.trans hH⟩, ?_⟩
    rw [Nat.le_div_iff_mul_le hp] at h1; rwa [mul_comm]
  · rintro ⟨⟨h0, _⟩, h1⟩
    refine ⟨h0, ?_⟩
    rw [Nat.le_div_iff_mul_le hp, mul_comm]; exact h1

theorem sum_log_sq_le (U : ℕ) (hU : 1 ≤ U) :
    ∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p ^ 2 ≤ U * Real.log (2 * U) ^ 2 := by
  calc ∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p ^ 2
      ≤ ∑ p ∈ Ioc U (2 * U), Real.log p ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ p ∈ Ioc U (2 * U), Real.log (2 * U) ^ 2 := by
        apply sum_le_sum; intro p hp
        rw [mem_Ioc] at hp
        have h0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
        have h1 := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast (by omega : 1 ≤ p))
        have h2 : Real.log p ≤ Real.log (2 * U) :=
          Real.log_le_log h0 (by exact_mod_cast hp.2)
        exact pow_le_pow_left₀ h1 h2 2
    _ = U * Real.log (2 * U) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * U - U = U by omega]

theorem sqrt_term_le (j : ℕ) :
    Real.sqrt ((32 + 64 * j) / 2 ^ j) ≤ 8 * ((j : ℝ) + 1) * (3 / 4) ^ j := by
  have h1 : (32 + 64 * (j : ℝ)) / 2 ^ j ≤ (8 * ((j : ℝ) + 1) * (3 / 4) ^ j) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (8 * ((j : ℝ) + 1) * (3 / 4) ^ j) ^ 2 * 2 ^ j =
        64 * ((j : ℝ) + 1) ^ 2 * (9 / 8) ^ j := by
      have : ((3 / 4 : ℝ) ^ j) ^ 2 * 2 ^ j = (9 / 8) ^ j := by
        rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]; norm_num
      calc (8 * ((j : ℝ) + 1) * (3 / 4) ^ j) ^ 2 * 2 ^ j
          = 64 * ((j : ℝ) + 1) ^ 2 * (((3 / 4 : ℝ) ^ j) ^ 2 * 2 ^ j) := by ring
        _ = _ := by rw [this]
    have h98 : (1 : ℝ) ≤ (9 / 8) ^ j := one_le_pow₀ (by norm_num)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [h2]; nlinarith
  calc _ ≤ Real.sqrt ((8 * ((j : ℝ) + 1) * (3 / 4) ^ j) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

theorem sum_sq_geom (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 1) ^ 2 * (3 / 4) ^ j ≤ 112 := by
  have key : ∀ J : ℕ, ∑ j ∈ range J, ((j : ℝ) + 1) ^ 2 * (3 / 4) ^ j =
      112 - (4 * (J : ℝ) ^ 2 + 32 * J + 112) * (3 / 4) ^ J := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring
  rw [key]
  have : 0 ≤ (4 * (J : ℝ) ^ 2 + 32 * J + 112) * (3 / 4) ^ J := by positivity
  linarith

theorem sum_sqrt_two_pow (J : ℕ) :
    ∑ j ∈ range J, Real.sqrt (2 ^ j) ≤ 3 * Real.sqrt (2 ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have h2 : Real.sqrt (2 ^ (J + 1)) = Real.sqrt 2 * Real.sqrt (2 ^ J) := by
      rw [pow_succ, mul_comm, Real.sqrt_mul (by norm_num)]
    have hs2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h0 := Real.sqrt_nonneg ((2 : ℝ) ^ J)
    rw [h2]; nlinarith

/-- `∑_{1 < x ≤ 2^J} g(x) = ∑_{j < J} ∑_{2^j < x ≤ 2^{j+1}} g(x)`. -/
theorem sum_Ioc_dyadic (g : ℕ → ℂ) (J : ℕ) :
    ∑ x ∈ Ioc 1 (2 ^ J), g x = ∑ j ∈ range J, ∑ x ∈ Ioc (2 ^ j) (2 * 2 ^ j), g x := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, mul_comm (2 ^ J) 2,
      sum_Ioc_consecutive _ Nat.one_le_two_pow (by omega)]

/-- **One dyadic block of small primes.** -/
theorem block_small (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} {a : ℚ}
    (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (N j : ℕ) :
    ‖∑ p ∈ Ioc (2 ^ j : ℕ) (2 * 2 ^ j) with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤
      ((j : ℝ) + 1) * (Real.sqrt (7 * N * 2 ^ j) + N * Real.sqrt (24 / a.den) +
        N * Real.sqrt ((32 + 64 * j) / 2 ^ j) + Real.sqrt ((8 + 16 * j) * N * a.den)) := by
  set U : ℕ := 2 ^ j with hUdef
  set r : ℕ := a.den with hrdef
  set H : ℕ := N / U with hHdef
  have hU1 : 1 ≤ U := Nat.one_le_two_pow
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hUc : (U : ℝ) = 2 ^ j := by simp [hUdef]
  set B : ℕ → ℂ := fun x => ∑ m ∈ Ioc 0 H, (if x * m ≤ N then f m * e (x * m * α) else 0)
    with hBdef
  have hB : ∀ p ∈ Ioc U (2 * U), ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α) = B p := by
    intro p hp
    rw [mem_Ioc] at hp
    exact sum_Ioc_div_eq N p H (by omega) (Nat.div_le_div_left hp.1.le (by omega)) _
  -- triangle inequality
  have hstep1 : ‖∑ p ∈ Ioc U (2 * U) with p.Prime,
      (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤
      ∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p * ‖B p‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun p hp => ?_)
    rw [mem_filter] at hp
    rw [hB p hp.1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have := mul_le_mul_of_nonneg_left (hfb p) (Real.log_natCast_nonneg p)
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (B p))
    linarith
  -- Cauchy–Schwarz over `p`
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt ((Ioc U (2 * U)).filter Nat.Prime)
    (fun p => Real.log p) (fun p => ‖B p‖)
  have hU1' : (1 : ℝ) ≤ U := by exact_mod_cast hU1
  have hlog2U : 0 ≤ Real.log (2 * U) := Real.log_nonneg (by linarith)
  have hS1 : Real.sqrt (∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p ^ 2) ≤
      Real.sqrt U * Real.log (2 * U) := by
    calc _ ≤ Real.sqrt (U * Real.log (2 * U) ^ 2) := Real.sqrt_le_sqrt (sum_log_sq_le U hU1)
      _ = Real.sqrt U * Real.log (2 * U) := by
          rw [Real.sqrt_mul hU0.le, Real.sqrt_sq hlog2U]
  -- the bilinear bound over all `x ∈ (U, 2U]`
  have hbil := bilinear_wt U (2 * U) N hU0 (by push_cast; linarith) (Ioc 0 H)
    (fun v hv => (mem_Ioc.1 hv).1) f α
  have hS2 : ∑ p ∈ Ioc U (2 * U) with p.Prime, ‖B p‖ ^ 2 ≤
      (H : ℝ) * (U + 2 * ((4 * H / r + 1) * (3 * U + 4 * r + 8 * r * j))) := by
    calc ∑ p ∈ Ioc U (2 * U) with p.Prime, ‖B p‖ ^ 2
        ≤ ∑ x ∈ Ioc U (2 * U), ‖B x‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ v ∈ Ioc 0 H, ∑ v' ∈ Ioc 0 H, ‖f v‖ * ‖f v'‖ * wt U (((v : ℝ) - v') * α) := hbil
      _ ≤ ∑ v ∈ Ioc 0 H, ∑ v' ∈ Ioc 0 H, wt U (((v : ℝ) - v') * α) := by
          apply sum_le_sum; intro v _; apply sum_le_sum; intro v' _
          have hw := wt_nonneg hU0.le (((v : ℝ) - v') * α)
          have h1 : ‖f v‖ * ‖f v'‖ ≤ 1 := by
            have := mul_le_mul (hfb v) (hfb v') (norm_nonneg _) zero_le_one
            linarith
          nlinarith
      _ ≤ H * (U + 2 * ∑ h ∈ Icc 1 H, wt U (h * α)) := double_sum_wt H hU0 α
      _ ≤ H * (U + 2 * ((4 * H / r + 1) * (3 * U + 4 * r + 8 * r * j))) := by
          have := sum_wt_le hα hr H hU0 j (by rw [hUc])
          gcongr
  -- algebra
  have hHU : (H : ℝ) * U ≤ N := by exact_mod_cast Nat.div_mul_le_self N U
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set Q : ℝ := (H : ℝ) * (U + 2 * ((4 * H / r + 1) * (3 * U + 4 * r + 8 * r * j))) with hQ
  have hUQ : U * Q ≤ 7 * N * U + N ^ 2 * (24 / r) + N ^ 2 * ((32 + 64 * j) / U) +
      (8 + 16 * j) * N * r := by
    have e1 : U * Q = U * (U * H) + 2 * (U * H) * (3 * U + 4 * r + 8 * r * j) +
        8 * (U * H) ^ 2 * (3 * U + 4 * r + 8 * r * j) / (U * r) := by
      rw [hQ]; field_simp; ring
    have hx0 : 0 ≤ (U : ℝ) * H := by positivity
    have hx : (U : ℝ) * H ≤ N := by linarith [mul_comm (U : ℝ) H]
    have hc : 0 ≤ 3 * (U : ℝ) + 4 * r + 8 * r * j := by positivity
    have t1 : (U : ℝ) * (U * H) ≤ U * N := mul_le_mul_of_nonneg_left hx hU0.le
    have t2 : 2 * ((U : ℝ) * H) * (3 * U + 4 * r + 8 * r * j) ≤
        2 * N * (3 * U + 4 * r + 8 * r * j) := by gcongr
    have t3 : 8 * ((U : ℝ) * H) ^ 2 * (3 * U + 4 * r + 8 * r * j) / (U * r) ≤
        8 * (N : ℝ) ^ 2 * (3 * U + 4 * r + 8 * r * j) / (U * r) := by gcongr
    have e2 : 8 * (N : ℝ) ^ 2 * (3 * U + 4 * r + 8 * r * j) / (U * r) =
        N ^ 2 * (24 / r) + N ^ 2 * ((32 + 64 * j) / U) := by field_simp; ring
    rw [e1]; nlinarith
  -- square roots
  have hfin : Real.sqrt U * Real.sqrt Q ≤ Real.sqrt (7 * N * 2 ^ j) + N * Real.sqrt (24 / r) +
      N * Real.sqrt ((32 + 64 * j) / 2 ^ j) + Real.sqrt ((8 + 16 * j) * N * r) := by
    rw [← Real.sqrt_mul hU0.le, ← hUc]
    have a1 : (0 : ℝ) ≤ 7 * N * U := by positivity
    have a2 : (0 : ℝ) ≤ N ^ 2 * (24 / r) := by positivity
    have a3 : (0 : ℝ) ≤ N ^ 2 * ((32 + 64 * j) / U) := by positivity
    have a4 : (0 : ℝ) ≤ (8 + 16 * j) * N * r := by positivity
    calc Real.sqrt (U * Q) ≤ Real.sqrt (7 * N * U + N ^ 2 * (24 / r) +
          N ^ 2 * ((32 + 64 * j) / U) + (8 + 16 * j) * N * r) := Real.sqrt_le_sqrt hUQ
      _ ≤ Real.sqrt (7 * N * U) + Real.sqrt (N ^ 2 * (24 / r)) +
          Real.sqrt (N ^ 2 * ((32 + 64 * j) / U)) + Real.sqrt ((8 + 16 * j) * N * r) := by
          refine (sqrt_add_le' (add_nonneg (add_nonneg a1 a2) a3) a4).trans ?_
          refine add_le_add ((sqrt_add_le' (add_nonneg a1 a2) a3).trans ?_) le_rfl
          exact add_le_add (sqrt_add_le' a1 a2) le_rfl
      _ = _ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN0]
  have hlogj : Real.log (2 * U) ≤ (j : ℝ) + 1 := by
    rw [hUc, ← pow_succ']
    rw [Real.log_pow]; push_cast
    have := Real.log_two_lt_d9
    nlinarith
  have hSQ : Real.sqrt (∑ p ∈ Ioc U (2 * U) with p.Prime, ‖B p‖ ^ 2) ≤ Real.sqrt Q :=
    Real.sqrt_le_sqrt hS2
  have hP0 : 0 ≤ Real.sqrt (7 * N * 2 ^ j) + N * Real.sqrt (24 / r) +
      N * Real.sqrt ((32 + 64 * j) / 2 ^ j) + Real.sqrt ((8 + 16 * j) * N * r) := by positivity
  calc _ ≤ ∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p * ‖B p‖ := hstep1
    _ ≤ Real.sqrt (∑ p ∈ Ioc U (2 * U) with p.Prime, Real.log p ^ 2) *
        Real.sqrt (∑ p ∈ Ioc U (2 * U) with p.Prime, ‖B p‖ ^ 2) := hCS
    _ ≤ (Real.sqrt U * Real.log (2 * U)) * Real.sqrt Q :=
        mul_le_mul hS1 hSQ (Real.sqrt_nonneg _) (by positivity)
    _ = Real.log (2 * U) * (Real.sqrt U * Real.sqrt Q) := by ring
    _ ≤ ((j : ℝ) + 1) * (Real.sqrt (7 * N * 2 ^ j) + N * Real.sqrt (24 / r) +
        N * Real.sqrt ((32 + 64 * j) / 2 ^ j) + Real.sqrt ((8 + 16 * j) * N * r)) :=
        mul_le_mul hlogj hfin (by positivity) (by positivity)

/-- **The small primes** `p ≤ 2^J`. -/
theorem small_primes (f : ℕ → ℂ) (hfb : ∀ n, ‖f n‖ ≤ 1) {α : ℝ} {a : ℚ}
    (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (N J : ℕ) :
    ‖∑ p ∈ Ioc 1 (2 ^ J : ℕ) with p.Prime,
        (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α)‖ ≤
      3 * Real.sqrt 7 * J * Real.sqrt (N * 2 ^ J) + (J : ℝ) ^ 2 * N * Real.sqrt (24 / a.den) +
        896 * N + (J : ℝ) ^ 2 * Real.sqrt (24 * J * N * a.den) := by
  set r : ℕ := a.den with hrdef
  set F : ℕ → ℂ := fun p =>
    (Real.log p : ℂ) * f p * ∑ m ∈ Ioc 0 (N / p), f m * e (p * m * α) with hF
  have hsplit : ∑ p ∈ Ioc 1 (2 ^ J) with p.Prime, F p =
      ∑ j ∈ range J, ∑ p ∈ Ioc (2 ^ j) (2 * 2 ^ j) with p.Prime, F p := by
    rw [sum_filter, sum_Ioc_dyadic]
    exact sum_congr rfl fun j _ => (sum_filter _ _).symm
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hjJ : ∀ j ∈ range J, (j : ℝ) + 1 ≤ J := by
    intro j hj; rw [mem_range] at hj; exact_mod_cast hj
  rw [hsplit]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun j _ => block_small f hfb hα hr N j).trans ?_)
  simp only [mul_add, sum_add_distrib]
  -- the four sums
  have s1 : ∑ j ∈ range J, ((j : ℝ) + 1) * Real.sqrt (7 * N * 2 ^ j) ≤
      3 * Real.sqrt 7 * J * Real.sqrt (N * 2 ^ J) := by
    calc ∑ j ∈ range J, ((j : ℝ) + 1) * Real.sqrt (7 * N * 2 ^ j)
        ≤ ∑ j ∈ range J, (J : ℝ) * (Real.sqrt (7 * N) * Real.sqrt (2 ^ j)) := by
          apply sum_le_sum; intro j hj
          rw [← Real.sqrt_mul (by positivity)]
          exact mul_le_mul_of_nonneg_right (hjJ j hj) (Real.sqrt_nonneg _)
      _ = J * Real.sqrt (7 * N) * ∑ j ∈ range J, Real.sqrt (2 ^ j) := by
          rw [mul_sum]; apply sum_congr rfl; intro j _; ring
      _ ≤ J * Real.sqrt (7 * N) * (3 * Real.sqrt (2 ^ J)) :=
          mul_le_mul_of_nonneg_left (sum_sqrt_two_pow J) (by positivity)
      _ = 3 * Real.sqrt 7 * J * Real.sqrt (N * 2 ^ J) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_mul hN0]; ring
  have s2 : ∑ j ∈ range J, ((j : ℝ) + 1) * (N * Real.sqrt (24 / r)) ≤
      (J : ℝ) ^ 2 * N * Real.sqrt (24 / r) := by
    calc ∑ j ∈ range J, ((j : ℝ) + 1) * (N * Real.sqrt (24 / r))
        ≤ ∑ j ∈ range J, (J : ℝ) * (N * Real.sqrt (24 / r)) :=
          sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hjJ j hj) (by positivity)
      _ = (J : ℝ) ^ 2 * N * Real.sqrt (24 / r) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
  have s3 : ∑ j ∈ range J, ((j : ℝ) + 1) * (N * Real.sqrt ((32 + 64 * j) / 2 ^ j)) ≤
      896 * N := by
    calc ∑ j ∈ range J, ((j : ℝ) + 1) * (N * Real.sqrt ((32 + 64 * j) / 2 ^ j))
        ≤ ∑ j ∈ range J, 8 * N * (((j : ℝ) + 1) ^ 2 * (3 / 4) ^ j) := by
          apply sum_le_sum; intro j _
          have := sqrt_term_le j
          have hj1 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
          calc ((j : ℝ) + 1) * (N * Real.sqrt ((32 + 64 * j) / 2 ^ j))
              ≤ ((j : ℝ) + 1) * (N * (8 * ((j : ℝ) + 1) * (3 / 4) ^ j)) := by gcongr
            _ = _ := by ring
      _ = 8 * N * ∑ j ∈ range J, ((j : ℝ) + 1) ^ 2 * (3 / 4) ^ j := by rw [mul_sum]
      _ ≤ 8 * N * 112 := mul_le_mul_of_nonneg_left (sum_sq_geom J) (by positivity)
      _ = 896 * N := by ring
  have s4 : ∑ j ∈ range J, ((j : ℝ) + 1) * Real.sqrt ((8 + 16 * j) * N * r) ≤
      (J : ℝ) ^ 2 * Real.sqrt (24 * J * N * r) := by
    calc ∑ j ∈ range J, ((j : ℝ) + 1) * Real.sqrt ((8 + 16 * j) * N * r)
        ≤ ∑ j ∈ range J, (J : ℝ) * Real.sqrt (24 * J * N * r) := by
          apply sum_le_sum; intro j hj
          have h1 := hjJ j hj
          apply mul_le_mul h1 _ (Real.sqrt_nonneg _) hJ0
          apply Real.sqrt_le_sqrt
          have : (8 + 16 * (j : ℝ)) ≤ 24 * J := by linarith
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hN0 hr0)
          nlinarith
      _ = (J : ℝ) ^ 2 * Real.sqrt (24 * J * N * r) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
  linarith

end Vinogradov.MV
