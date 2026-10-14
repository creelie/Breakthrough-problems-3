import Vinogradov.PV.Polya

/-!
# The Pólya–Vinogradov inequality with `log log q`

For a primitive character `χ` modulo `q ≥ 3`, `‖∑_{n ≤ T} χ(n)‖ ≤ C √q log log q`, assuming
Montgomery–Vaughan's bound for exponential sums with multiplicative coefficients
[MV77, Corollary 1], stated below as `MVBound`. The zero-free half-plane `Re s > 7/8` enters
through `nonsmooth_major` (the major arcs); `MVBound` covers the minor arcs.
-/

namespace Vinogradov.PV

open Finset Complex

theorem gpf_le_self (n : ℕ) : gpf n ≤ n :=
  Finset.sup_le fun _ hp => Nat.le_of_mem_primeFactors hp

theorem harmonic_real_le (N : ℕ) : ∑ n ∈ Ioc 0 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have hI : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [hI]; simpa [one_div] using h

theorem norm_mul_e_le {q : ℕ} (χ : DirichletCharacter ℂ q) (β : ℝ) (n : ℕ) :
    ‖(χ n : ℂ) * e (n * β)‖ ≤ 1 := by
  rw [norm_mul, norm_e, mul_one]; exact DirichletCharacter.norm_le_one χ _

/-- `0 ≤ 1/t - 1/(t+1) ≤ 1/t²` for `t ≥ 1`. -/
theorem weight_nonneg {t : ℕ} (ht : 1 ≤ t) : 0 ≤ 1 / (t : ℝ) - 1 / ((t : ℝ) + 1) := by
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem weight_eq {t : ℕ} (ht : 1 ≤ t) :
    1 / (t : ℝ) - 1 / ((t : ℝ) + 1) = 1 / ((t : ℝ) * ((t : ℝ) + 1)) := by
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  field_simp; ring

/-- **Abel summation for the integers with a large prime factor.** -/
theorem abel_nonsmooth (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (Y H : ℕ) :
    ‖∑ n ∈ Ioc 0 H with Y < gpf n, f n / n‖ ≤
      1 + ∑ t ∈ Ico 1 H, ‖∑ n ∈ Ioc 0 t with Y < gpf n, f n‖ *
        (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) := by
  classical
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  set a : ℕ → ℂ := fun n => if Y < gpf n then f n else 0 with ha
  have hA : ∀ t, ∑ n ∈ Ioc 0 t with Y < gpf n, f n = ∑ k ∈ Ioc 0 t, a k := fun t => by
    rw [sum_filter]
  have hS : ∑ n ∈ Ioc 0 H with Y < gpf n, f n / n =
      ∑ n ∈ Ioc 0 H, a n * (fun n : ℕ => (1 : ℂ) / n) n := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [a]; split_ifs <;> simp only [zero_mul, div_eq_mul_inv, one_mul]
  rw [hS, abel_identity _ _ (Nat.zero_le H), sum_eq_sum_Ico_succ_bot hH]
  simp only [Ioc_self, sum_empty, zero_mul, zero_add]
  have hnA : ∀ t, ‖∑ k ∈ Ioc 0 t, a k‖ ≤ t := fun t => by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Ioc 0 t, ‖a k‖ ≤ ∑ k ∈ Ioc 0 t, (1 : ℝ) := sum_le_sum fun k _ => by
          simp only [a]; split_ifs
          · exact hf k
          · simp
      _ = t := by simp
  have hg : ∀ n, 1 ≤ n → ‖(1 : ℂ) / ((n + 1 : ℕ) : ℂ) - 1 / (n : ℂ)‖ =
      1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
    intro n hn
    have h : (1 : ℂ) / ((n + 1 : ℕ) : ℂ) - 1 / (n : ℂ) =
        ((-(1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (weight_nonneg hn)]
  calc _ ≤ ‖(∑ k ∈ Ioc 0 H, a k) * ((1 : ℂ) / (H : ℂ))‖ +
        ‖∑ n ∈ Ico 1 H, (∑ k ∈ Ioc 0 n, a k) * ((1 : ℂ) / ((n + 1 : ℕ) : ℂ) - 1 / (n : ℂ))‖ :=
        norm_sub_le _ _
    _ ≤ 1 + ∑ n ∈ Ico 1 H, ‖∑ k ∈ Ioc 0 n, a k‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
        gcongr
        · rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
          have hH' : (0 : ℝ) < H := by exact_mod_cast hH
          calc ‖∑ k ∈ Ioc 0 H, a k‖ * (1 / (H : ℝ)) ≤ H * (1 / (H : ℝ)) := by
                gcongr; exact hnA H
            _ = 1 := by field_simp
        · refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n hn => ?_))
          rw [norm_mul, hg n (mem_Ico.mp hn).1]
    _ = _ := by simp only [hA]

/-- The counting function of the smooth numbers, summed against `1/t - 1/(t+1)`. -/
theorem psi_abel (Y H : ℕ) :
    ∑ t ∈ Ico 1 H, (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) *
        (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) ≤
      ∑ n ∈ Ioc 0 H with gpf n ≤ Y, (1 : ℝ) / n := by
  classical
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · simp
  set a : ℕ → ℝ := fun n => if gpf n ≤ Y then 1 else 0 with ha
  have hA : ∀ t, (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) = ∑ k ∈ Ioc 0 t, a k :=
    fun t => by simp only [a]; rw [sum_boole]
  have hS : ∑ n ∈ Ioc 0 H with gpf n ≤ Y, (1 : ℝ) / n =
      ∑ n ∈ Ioc 0 H, a n * (fun n : ℕ => (1 : ℝ) / n) n := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [a]; split_ifs <;> simp
  rw [hS, abel_identity_real _ _ (Nat.zero_le H), sum_eq_sum_Ico_succ_bot hH]
  simp only [Ioc_self, sum_empty, zero_mul, zero_add]
  have h0 : 0 ≤ (∑ k ∈ Ioc 0 H, a k) * (1 / (H : ℝ)) := by
    rw [← hA]; positivity
  have h2 : ∑ n ∈ Ico 1 H, (∑ k ∈ Ioc 0 n, a k) * (1 / ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ)) =
      -∑ t ∈ Ico 1 H, (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) *
        (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← hA]; push_cast; ring
  rw [h2]; linarith

/-- **Montgomery–Vaughan** [MV77, Corollary 1], for `f = χ`: if `(a, r) = 1`,
`|α - a/r| ≤ r⁻²` and `2 ≤ R ≤ r ≤ N/R`, then
`‖∑_{n ≤ N} χ(n) e(nα)‖ ≤ C (N / log N + N (log R)^{3/2} / √R)`.
H. L. Montgomery and R. C. Vaughan, *Exponential sums with multiplicative coefficients*,
Invent. Math. 43 (1977), 69–82. -/
def MVBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (α : ℝ) (a : ℚ) (N : ℕ)
    (R : ℝ), 2 ≤ R → R ≤ a.den → (a.den : ℝ) ≤ N / R → |α - a| ≤ 1 / (a.den : ℝ) ^ 2 →
      ‖∑ n ∈ Ioc 0 N, (χ n : ℂ) * e (n * α)‖ ≤
        C * (N / Real.log N + N * Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R)

/-- **The partial sums over integers with a large prime factor.** For `t > Y ≥ R`, by Dirichlet's
theorem with `Q = ⌊t/R⌋`: a major arc is `nonsmooth_major`, a minor arc is `MVBound` less the
smooth numbers. -/
theorem partial_le (hMV : MVBound) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ (R : ℝ) (Y : ℕ), 2 ≤ R → R < q → R ≤ Y → ∀ (β : ℝ) (t : ℕ), Y < t →
        ‖∑ n ∈ Ioc 0 t with Y < gpf n, (χ n : ℂ) * e (n * β)‖ ≤
          C₁ * (t / Real.log t + t * (Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R)) +
            (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) +
            C₂ * (R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) /
              ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y)) * t := by
  classical
  obtain ⟨C₁, hC₁, hmv⟩ := hMV
  obtain ⟨C₂, hC₂, hmaj⟩ := nonsmooth_major
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro q _ χ hχ R Y hR hRq hRY β t hYt
  have hYt' : (Y : ℝ) < t := by exact_mod_cast hYt
  have hRt : R < t := hRY.trans_lt hYt'
  have hR0 : 0 < R := by linarith
  have hY2 : (2 : ℝ) ≤ Y := hR.trans hRY
  have hY2' : 2 ≤ Y := by exact_mod_cast hY2
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  -- the three terms are nonnegative
  have hT1 : 0 ≤ C₁ * (t / Real.log t + t * (Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R)) := by
    have := Real.log_nonneg ht1
    have := Real.log_nonneg (show (1 : ℝ) ≤ R by linarith)
    positivity
  have hT2 : (0 : ℝ) ≤ (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) := by positivity
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlqR : 0 ≤ Real.log (q * R + 2) := Real.log_nonneg (by nlinarith)
  have hT3 : 0 ≤ C₂ * (R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) /
      ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y)) * t := by positivity
  -- Dirichlet's approximation
  set Q : ℕ := ⌊(t : ℝ) / R⌋₊ with hQ
  have hQ0 : 0 < Q := Nat.floor_pos.mpr (by rw [le_div_iff₀ hR0]; linarith)
  obtain ⟨a, ha, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le β hQ0
  have hd0 : (0 : ℝ) < a.den := by exact_mod_cast a.den_pos
  have hdQ : (a.den : ℝ) ≤ Q := by exact_mod_cast hden
  have hQt : (Q : ℝ) ≤ t / R := Nat.floor_le (by positivity)
  have hQt' : (t : ℝ) / R < Q + 1 := Nat.lt_floor_add_one _
  by_cases hmin : R < a.den
  · -- minor arc
    have hβ : |β - a| ≤ 1 / (a.den : ℝ) ^ 2 := by
      refine ha.trans (one_div_le_one_div_of_le (by positivity) ?_)
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hd0.le
    have hS := hmv q χ β a t R hR hmin.le (hdQ.trans hQt) hβ
    have hsplit := sum_filter_add_sum_filter_not (Ioc 0 t) (fun n => Y < gpf n)
      (fun n => (χ n : ℂ) * e (n * β))
    have hsm : ‖∑ n ∈ Ioc 0 t with ¬ Y < gpf n, (χ n : ℂ) * e (n * β)‖ ≤
        (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ n ∈ Ioc 0 t with ¬ Y < gpf n, (1 : ℝ) :=
            sum_le_sum fun n _ => norm_mul_e_le χ β n
        _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, not_lt]
    have hA : ∑ n ∈ Ioc 0 t with Y < gpf n, (χ n : ℂ) * e (n * β) =
        ∑ n ∈ Ioc 0 t, (χ n : ℂ) * e (n * β) -
          ∑ n ∈ Ioc 0 t with ¬ Y < gpf n, (χ n : ℂ) * e (n * β) := by
      rw [← hsplit]; ring
    rw [hA]
    calc _ ≤ ‖∑ n ∈ Ioc 0 t, (χ n : ℂ) * e (n * β)‖ +
          ‖∑ n ∈ Ioc 0 t with ¬ Y < gpf n, (χ n : ℂ) * e (n * β)‖ := norm_sub_le _ _
      _ ≤ C₁ * (t / Real.log t + t * (Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R)) +
          (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) := by
          refine add_le_add (hS.trans (le_of_eq ?_)) hsm
          ring
      _ ≤ _ := by linarith
  · -- major arc
    push Not at hmin
    have hdq : a.den < q := by
      have : (a.den : ℝ) < q := hmin.trans_lt hRq
      exact_mod_cast this
    have hdY : a.den ≤ Y := by
      have : (a.den : ℝ) ≤ Y := hmin.trans hRY
      exact_mod_cast this
    have hM := hmaj q χ hχ a.den a.den_pos hdq a.num (β - a) Y t hY2' hdY
    have hα : ((a.num : ℤ) : ℝ) / ((a.den : ℕ) : ℝ) + (β - a) = β := by
      rw [Rat.cast_def]; ring
    rw [hα] at hM
    have hbt : |β - a| * t ≤ R := by
      have h1 : |β - a| ≤ 1 / ((Q : ℝ) + 1) := by
        refine ha.trans (one_div_le_one_div_of_le (by positivity) ?_)
        have : (1 : ℝ) ≤ a.den := by exact_mod_cast a.den_pos
        nlinarith
      have h2 : (t : ℝ) < R * ((Q : ℝ) + 1) := by rwa [div_lt_iff₀ hR0, mul_comm] at hQt'
      calc |β - a| * t ≤ 1 / ((Q : ℝ) + 1) * t := by gcongr
        _ ≤ R := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
    have hlq : Real.log (q * a.den + 2) ≤ Real.log (q * R + 2) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hY20 : 0 < (Y : ℝ) ^ (1 / 20 : ℝ) := by positivity
    have hP : 2 + 2 * Real.pi * |β - a| * t ≤ 2 + 2 * Real.pi * R := by
      have := Real.pi_pos
      have h : 2 * Real.pi * |β - a| * t = 2 * Real.pi * (|β - a| * t) := by ring
      rw [h]; gcongr
    have hlq0 : 0 ≤ Real.log (q * a.den + 2) := Real.log_nonneg (by nlinarith)
    have hnum : C₂ * a.den * Real.log (q * a.den + 2) * (2 + 2 * Real.pi * |β - a| * t) * t ≤
        C₂ * R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) * t := by
      have h1 : (a.den : ℝ) * Real.log (q * a.den + 2) ≤ R * Real.log (q * R + 2) :=
        mul_le_mul hmin hlq hlq0 hR0.le
      have h2 : (a.den : ℝ) * Real.log (q * a.den + 2) * (2 + 2 * Real.pi * |β - a| * t) ≤
          R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) :=
        mul_le_mul h1 hP (by positivity) (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 hC₂.le
      have h4 := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ t by positivity)
      calc _ = C₂ * ((a.den : ℝ) * Real.log (q * a.den + 2) *
            (2 + 2 * Real.pi * |β - a| * t)) * t := by ring
        _ ≤ C₂ * (R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R)) * t := h4
        _ = _ := by ring
    calc _ ≤ C₂ * a.den * Real.log (q * a.den + 2) * (2 + 2 * Real.pi * |β - a| * t) * t /
          ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) := hM
      _ ≤ C₂ * R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) * t /
          ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = C₂ * (R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) /
          ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y)) * t := by ring
      _ ≤ _ := by linarith

/-! ### The parameters `R = M⁴`, `Y = M²⁰⁰`, `M = ⌈log q⌉` -/

theorem one_le_log_of_ge {M : ℝ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log M :=
      Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)

theorem one_lt_log_three : 1 < Real.log 3 := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)

theorem rho_bound {M L : ℝ} (hM : 200 ≤ M) (hLM : L ≤ M) (hL : 0 ≤ L) :
    Real.log (M ^ 4) ^ (3 / 2 : ℝ) / Real.sqrt (M ^ 4) * (1 + L) ≤ 128 := by
  have hM0 : 0 < M := by linarith
  have hℓ1 : 1 ≤ Real.log M := one_le_log_of_ge (by linarith)
  have hlog4 : Real.log (M ^ 4) = 4 * Real.log M := by rw [Real.log_pow]; norm_num
  have hsqrt : Real.sqrt (M ^ 4) = M ^ 2 := by
    rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpow : (4 * Real.log M) ^ (3 / 2 : ℝ) ≤ (4 * Real.log M) ^ 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hℓsq : Real.log M ^ 2 ≤ 4 * M := by
    have h := Real.log_le_rpow_div hM0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    have h' : Real.log M ≤ 2 * Real.sqrt M := by
      calc Real.log M ≤ Real.sqrt M / (1 / 2) := h
        _ = 2 * Real.sqrt M := by ring
    calc Real.log M ^ 2 ≤ (2 * Real.sqrt M) ^ 2 := pow_le_pow_left₀ (by linarith) h' 2
      _ = 4 * M := by rw [mul_pow, Real.sq_sqrt hM0.le]; ring
  rw [hlog4, hsqrt]
  have hM2 : 0 < M ^ 2 := by positivity
  calc (4 * Real.log M) ^ (3 / 2 : ℝ) / M ^ 2 * (1 + L)
      ≤ (4 * Real.log M) ^ 2 / M ^ 2 * (2 * M) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hpow hM2.le) (by linarith) (by linarith)
        positivity
    _ = 32 * Real.log M ^ 2 / M := by field_simp; ring
    _ ≤ 128 := by rw [div_le_iff₀ hM0]; linarith

theorem k_bound {M L q : ℝ} (hM : 200 ≤ M) (hLM : L ≤ M) (hL : 0 ≤ L) (hq : 1 ≤ q)
    (hlq : Real.log q ≤ M) :
    M ^ 4 * Real.log (q * M ^ 4 + 2) * (2 + 2 * Real.pi * M ^ 4) /
      ((M ^ 200) ^ (1 / 20 : ℝ) * Real.log (M ^ 200)) * (1 + L) ≤ 1 := by
  have hM0 : 0 < M := by linarith
  have hℓ1 : 1 ≤ Real.log M := one_le_log_of_ge (by linarith)
  have h20 : (M ^ 200) ^ (1 / 20 : ℝ) = M ^ 10 := by
    rw [show M ^ 200 = (M ^ 10) ^ 20 by ring, show (1 / 20 : ℝ) = ((20 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have hl200 : Real.log (M ^ 200) = 200 * Real.log M := by rw [Real.log_pow]; norm_num
  have hlogM : Real.log M ≤ M - 1 := Real.log_le_sub_one_of_pos hM0
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hM4 : 1 ≤ M ^ 4 := one_le_pow₀ (by linarith)
  have hlqM : Real.log (q * M ^ 4 + 2) ≤ 6 * M := by
    have h1 : q * M ^ 4 + 2 ≤ 3 * q * M ^ 4 := by nlinarith
    have h2 : Real.log (3 * q * M ^ 4) = Real.log 3 + Real.log q + 4 * Real.log M := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      norm_num
    calc Real.log (q * M ^ 4 + 2) ≤ Real.log (3 * q * M ^ 4) :=
          Real.log_le_log (by positivity) h1
      _ ≤ 6 * M := by rw [h2]; linarith
  have hM4' : M ≤ M ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hpi : 2 + 2 * Real.pi * M ^ 4 ≤ 8 * M ^ 4 := by
    have h := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le (show 0 ≤ M ^ 4 by positivity)
    linarith
  have hlq0 : 0 ≤ Real.log (q * M ^ 4 + 2) := Real.log_nonneg (by nlinarith)
  rw [h20, hl200, div_mul_eq_mul_div, div_le_iff₀ (by positivity), one_mul]
  have hP0 : 0 ≤ 2 + 2 * Real.pi * M ^ 4 := by positivity
  have e1 : M ^ 4 * Real.log (q * M ^ 4 + 2) ≤ M ^ 4 * (6 * M) :=
    mul_le_mul_of_nonneg_left hlqM (by positivity)
  have e2 : M ^ 4 * Real.log (q * M ^ 4 + 2) * (2 + 2 * Real.pi * M ^ 4) ≤
      M ^ 4 * (6 * M) * (8 * M ^ 4) := mul_le_mul e1 hpi hP0 (by positivity)
  have e3 : M ^ 4 * Real.log (q * M ^ 4 + 2) * (2 + 2 * Real.pi * M ^ 4) * (1 + L) ≤
      M ^ 4 * (6 * M) * (8 * M ^ 4) * (2 * M) := mul_le_mul e2 (by linarith) (by linarith)
        (by positivity)
  have e4 : 96 * M ^ 10 ≤ M ^ 10 * (200 * Real.log M) := by
    have := pow_pos hM0 10; nlinarith
  calc _ ≤ M ^ 4 * (6 * M) * (8 * M ^ 4) * (2 * M) := e3
    _ = 96 * M ^ 10 := by ring
    _ ≤ _ := e4

theorem logY_le {M L : ℝ} (hL : 200 ≤ L) (hM0 : 0 < M) (hML : M ≤ L + 1) :
    Real.log (M ^ 200) ≤ 400 * Real.log L := by
  rw [Real.log_pow]
  have h1 : M ≤ L ^ 2 := by nlinarith
  have h2 : Real.log M ≤ 2 * Real.log L := by
    calc Real.log M ≤ Real.log (L ^ 2) := Real.log_le_log hM0 h1
      _ = 2 * Real.log L := by rw [Real.log_pow]; norm_num
  push_cast; linarith

theorem pow_four_lt {M L q : ℝ} (hL : 200 ≤ L) (hM0 : 0 ≤ M) (hML : M ≤ L + 1) (hq : 0 < q)
    (hLq : Real.log q = L) : M ^ 4 < q := by
  have hqe : Real.exp L = q := by rw [← hLq, Real.exp_log hq]
  have h6 := Real.pow_div_factorial_le_exp L (show 0 ≤ L by linarith) 6
  rw [hqe] at h6
  norm_num [Nat.factorial] at h6
  have hM2 : M ^ 4 ≤ (2 * L) ^ 4 := pow_le_pow_left₀ hM0 (by linarith) 4
  have hL4 : 0 < L ^ 4 := by positivity
  have h7 : (2 * L) ^ 4 < L ^ 6 / 720 := by
    rw [lt_div_iff₀ (by norm_num)]
    have h6' : L ^ 6 = L ^ 4 * L ^ 2 := by ring
    have hL2 : (40000 : ℝ) ≤ L ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hL2 hL4.le
    rw [h6']; linarith
  linarith

/-- **Theorem B.** Under `MVBound`, for primitive `χ` modulo `q` with `log q ≥ 200`,
`‖∑_{m ≤ H} χ(m) e(mβ)/m‖ ≤ C log log q` for every `H ≤ q` and real `β`. -/
theorem hsum_bound (hMV : MVBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      200 ≤ Real.log q → ∀ H : ℕ, H ≤ q → ∀ β : ℝ,
        ‖∑ m ∈ Ioc 0 H, (χ m : ℂ) * e (m * β) / m‖ ≤ C * Real.log (Real.log q) := by
  classical
  obtain ⟨C₁, C₂, hC₁, hC₂, hpart⟩ := partial_le hMV
  refine ⟨800 * Real.exp 11 + 1 + 132 * C₁ + C₂, by positivity, ?_⟩
  intro q _ χ hχ hL H hHq β
  set L := Real.log q with hLdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Mn : ℕ := ⌈L⌉₊ with hMn
  have hLM : L ≤ (Mn : ℝ) := Nat.le_ceil L
  have hML : (Mn : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hM200 : (200 : ℝ) ≤ Mn := by linarith
  have hM0 : (0 : ℝ) < Mn := by linarith
  set Y : ℕ := Mn ^ 200 with hY
  have hYc : (Y : ℝ) = (Mn : ℝ) ^ 200 := by simp [hY]
  have hRq : (Mn : ℝ) ^ 4 < q := pow_four_lt hL hM0.le hML hq0 rfl
  have hR2 : (2 : ℝ) ≤ (Mn : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (Mn : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hRY : (Mn : ℝ) ^ 4 ≤ Y := by
    rw [hYc]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hY2 : (2 : ℝ) ≤ Y := hR2.trans hRY
  have hY2' : 2 ≤ Y := by exact_mod_cast hY2
  have hL0 : 0 ≤ L := by linarith
  set R : ℝ := (Mn : ℝ) ^ 4 with hR
  set ρ : ℝ := Real.log R ^ (3 / 2 : ℝ) / Real.sqrt R with hρ
  set k : ℝ := R * Real.log (q * R + 2) * (2 + 2 * Real.pi * R) /
    ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) with hk
  have hρb : ρ * (1 + L) ≤ 128 := rho_bound hM200 hLM hL0
  have hkb : k * (1 + L) ≤ 1 := by
    rw [hk, hYc]; exact k_bound hM200 hLM hL0 hq1 hLM
  have hlogY : Real.log Y ≤ 400 * Real.log L := by rw [hYc]; exact logY_le hL hM0 hML
  have hlogL : 1 ≤ Real.log L := one_le_log_of_ge (by linarith)
  have hρ0 : 0 ≤ ρ :=
    div_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _) (Real.sqrt_nonneg _)
  have hk0 : 0 ≤ k := by
    have h1 : 0 ≤ Real.log (q * R + 2) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
    have h3 : 0 ≤ 2 + 2 * Real.pi * R := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) h1) h3)
      (mul_nonneg (by positivity) h2)
  -- the large-prime-factor part, by Abel summation
  have hf1 : ∀ n, ‖(fun n : ℕ => (χ n : ℂ) * e (n * β)) n‖ ≤ 1 := fun n => norm_mul_e_le χ β n
  have hns := abel_nonsmooth (fun n : ℕ => (χ n : ℂ) * e (n * β)) hf1 Y H
  -- the smooth part
  have hsm : ‖∑ n ∈ Ioc 0 H with ¬ Y < gpf n, (χ n : ℂ) * e (n * β) / n‖ ≤
      Real.exp 11 * Real.log Y := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ n ∈ Ioc 0 H with gpf n ≤ Y, (1 : ℝ) / n := by
          simp only [not_lt]
          refine sum_le_sum fun n _ => ?_
          rw [norm_div, Complex.norm_natCast]
          exact div_le_div_of_nonneg_right (norm_mul_e_le χ β n) (Nat.cast_nonneg n)
      _ ≤ _ := smooth_sum_le H Y hY2'
  -- pointwise bound for the partial sums
  have hpt : ∀ t ∈ Ico 1 H, ‖∑ n ∈ Ioc 0 t with Y < gpf n, (χ n : ℂ) * e (n * β)‖ *
      (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) ≤
      C₁ * (1 / ((t : ℝ) * Real.log t)) + C₁ * ρ * (1 / (t : ℝ)) +
        (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) *
          (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) +
        C₂ * k * (1 / (t : ℝ)) := by
    intro t ht
    have ht1 : 1 ≤ t := (mem_Ico.mp ht).1
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have hw0 := weight_nonneg ht1
    have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1'
    have hP0 : 0 ≤ (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) *
        (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) := mul_nonneg (by positivity) hw0
    have hrest : 0 ≤ C₁ * ρ * (1 / (t : ℝ)) + C₂ * k * (1 / (t : ℝ)) :=
      add_nonneg (mul_nonneg (mul_nonneg hC₁.le hρ0) (by positivity))
        (mul_nonneg (mul_nonneg hC₂.le hk0) (by positivity))
    have hA1 : 0 ≤ C₁ * (1 / ((t : ℝ) * Real.log t)) := by positivity
    by_cases hYt : Y < t
    · have hb := hpart q χ hχ R Y hR2 hRq hRY β t hYt
      have e1 : (t : ℝ) / Real.log t * (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) ≤
          1 / ((t : ℝ) * Real.log t) := by
        rcases eq_or_lt_of_le hlt with h | h
        · rw [← h]; simp
        · have hwle : 1 / (t : ℝ) - 1 / ((t : ℝ) + 1) ≤ 1 / (t : ℝ) ^ 2 := by
            rw [weight_eq ht1]
            exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
          calc _ ≤ (t : ℝ) / Real.log t * (1 / (t : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_left hwle (by positivity)
            _ = _ := by field_simp
      have e2 : (t : ℝ) * (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) ≤ 1 / (t : ℝ) := by
        rw [weight_eq ht1]
        calc (t : ℝ) * (1 / ((t : ℝ) * ((t : ℝ) + 1))) = 1 / ((t : ℝ) + 1) := by
              field_simp
          _ ≤ 1 / (t : ℝ) := one_div_le_one_div_of_le (by positivity) (by linarith)
      have f1 := mul_le_mul_of_nonneg_left e1 hC₁.le
      have f2 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hC₁.le hρ0)
      have f3 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hC₂.le hk0)
      calc _ ≤ (C₁ * ((t : ℝ) / Real.log t + t * ρ) +
            (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) + C₂ * k * t) *
            (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) := mul_le_mul_of_nonneg_right hb hw0
        _ = C₁ * ((t : ℝ) / Real.log t * (1 / (t : ℝ) - 1 / ((t : ℝ) + 1))) +
            C₁ * ρ * ((t : ℝ) * (1 / (t : ℝ) - 1 / ((t : ℝ) + 1))) +
            (((Ioc 0 t).filter (fun n => gpf n ≤ Y)).card : ℝ) *
              (1 / (t : ℝ) - 1 / ((t : ℝ) + 1)) +
            C₂ * k * ((t : ℝ) * (1 / (t : ℝ) - 1 / ((t : ℝ) + 1))) := by ring
        _ ≤ _ := by linarith
    · push Not at hYt
      have hempty : (Ioc 0 t).filter (fun n => Y < gpf n) = ∅ := by
        refine filter_eq_empty_iff.mpr fun n hn => ?_
        have := gpf_le_self n; have := (mem_Ioc.mp hn).2; omega
      rw [hempty, sum_empty, norm_zero, zero_mul]
      linarith
  -- the three sums over `t`
  have hlogHL : Real.log H ≤ L := by
    rcases Nat.eq_zero_or_pos H with h | h
    · rw [h]; simp; linarith
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hHq)
  have hS1 : ∑ t ∈ Ico 1 H, 1 / ((t : ℝ) * Real.log t) ≤ 3 + Real.log L := by
    have hlogH : Real.log (Real.log H) ≤ Real.log L := by
      rcases Nat.lt_or_ge H 2 with h | h
      · interval_cases H <;> simpa using Real.log_nonneg (show (1 : ℝ) ≤ L by linarith)
      · have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast h
        exact Real.log_le_log (Real.log_pos (by linarith)) hlogHL
    calc _ ≤ ∑ t ∈ Ioc 0 H, 1 / ((t : ℝ) * Real.log t) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro t ht; simp only [mem_Ico, mem_Ioc] at ht ⊢; omega
          · intro t _ _; have := Real.log_natCast_nonneg t; positivity
      _ ≤ 3 + Real.log (Real.log H) := sum_inv_mul_log_le' H
      _ ≤ 3 + Real.log L := by linarith
  have hS2 : ∑ t ∈ Ico 1 H, 1 / (t : ℝ) ≤ 1 + L := by
    calc _ ≤ ∑ t ∈ Ioc 0 H, 1 / (t : ℝ) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro t ht; simp only [mem_Ico, mem_Ioc] at ht ⊢; omega
          · intro t _ _; positivity
      _ ≤ 1 + Real.log H := harmonic_real_le H
      _ ≤ 1 + L := by linarith
  have hS3 := (psi_abel Y H).trans (smooth_sum_le H Y hY2')
  have hS2' : 0 ≤ ∑ t ∈ Ico 1 H, 1 / (t : ℝ) := sum_nonneg fun t _ => by positivity
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum] at hsum
  -- assemble
  have g1 : C₁ * ∑ t ∈ Ico 1 H, 1 / ((t : ℝ) * Real.log t) ≤ C₁ * (3 + Real.log L) :=
    mul_le_mul_of_nonneg_left hS1 hC₁.le
  have g2 : C₁ * ρ * ∑ t ∈ Ico 1 H, 1 / (t : ℝ) ≤ C₁ * 128 := by
    calc _ ≤ C₁ * ρ * (1 + L) := mul_le_mul_of_nonneg_left hS2 (mul_nonneg hC₁.le hρ0)
      _ = C₁ * (ρ * (1 + L)) := by ring
      _ ≤ C₁ * 128 := mul_le_mul_of_nonneg_left hρb hC₁.le
  have g3 : C₂ * k * ∑ t ∈ Ico 1 H, 1 / (t : ℝ) ≤ C₂ := by
    calc _ ≤ C₂ * k * (1 + L) := mul_le_mul_of_nonneg_left hS2 (mul_nonneg hC₂.le hk0)
      _ = C₂ * (k * (1 + L)) := by ring
      _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hkb hC₂.le
      _ = C₂ := mul_one _
  have g4 : Real.exp 11 * Real.log Y ≤ Real.exp 11 * (400 * Real.log L) :=
    mul_le_mul_of_nonneg_left hlogY (Real.exp_pos 11).le
  have g5 : 1 + 131 * C₁ + C₂ ≤ (1 + 131 * C₁ + C₂) * Real.log L := by
    have := mul_le_mul_of_nonneg_left hlogL (show 0 ≤ 1 + 131 * C₁ + C₂ by positivity)
    linarith
  rw [← sum_filter_add_sum_filter_not (Ioc 0 H) (fun n => Y < gpf n)]
  calc _ ≤ ‖∑ n ∈ Ioc 0 H with Y < gpf n, (χ n : ℂ) * e (n * β) / n‖ +
        ‖∑ n ∈ Ioc 0 H with ¬ Y < gpf n, (χ n : ℂ) * e (n * β) / n‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

/-- **The Pólya–Vinogradov inequality with `log log q`**, under `MVBound`. -/
theorem polya_vinogradov_loglog (hMV : MVBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      3 ≤ q → ∀ T : ℕ,
        ‖∑ n ∈ Ioc 0 T, (χ n : ℂ)‖ ≤ C * Real.sqrt q * Real.log (Real.log q) := by
  obtain ⟨CB, hCB, hB⟩ := hsum_bound hMV
  have hc0 : 0 < Real.log (Real.log 3) := Real.log_pos one_lt_log_three
  refine ⟨max (CB + 6) (207 / Real.log (Real.log 3)), by positivity, ?_⟩
  intro q _ χ hχ hq3 T
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hsq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hLL : Real.log (Real.log 3) ≤ Real.log (Real.log q) :=
    Real.log_le_log (by linarith [one_lt_log_three]) (Real.log_le_log (by norm_num) hq)
  have hLL0 : 0 ≤ Real.log (Real.log q) := by linarith
  have hχi := isPrimitive_inv hχ
  by_cases hL : 200 ≤ Real.log q
  · have hb := polya_bound (by omega) hχ (B := CB * Real.log (Real.log q))
      (fun H hH β => hB q χ⁻¹ hχi hL H (by omega) β) T
    have hLL1 : 1 ≤ Real.log (Real.log q) := one_le_log_of_ge (by linarith)
    calc _ ≤ Real.sqrt q * (CB * Real.log (Real.log q) + 6) := hb
      _ ≤ Real.sqrt q * ((CB + 6) * Real.log (Real.log q)) :=
          mul_le_mul_of_nonneg_left (by linarith) hsq
      _ ≤ Real.sqrt q * (max (CB + 6) (207 / Real.log (Real.log 3)) * Real.log (Real.log q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hLL0) hsq
      _ = _ := by ring
  · push Not at hL
    have h201 : ∀ H : ℕ, 2 * H ≤ q → ∀ β : ℝ,
        ‖∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * β) / m‖ ≤ 201 := by
      intro H hH β
      have hlogH : Real.log H ≤ Real.log q := by
        rcases Nat.eq_zero_or_pos H with h | h
        · rw [h]; simp; exact Real.log_nonneg (by linarith)
        · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast (by omega : H ≤ q))
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ m ∈ Ioc 0 H, (1 : ℝ) / m := sum_le_sum fun m _ => by
            rw [norm_div, Complex.norm_natCast]
            exact div_le_div_of_nonneg_right (norm_mul_e_le χ⁻¹ β m) (Nat.cast_nonneg m)
        _ ≤ 1 + Real.log H := harmonic_real_le H
        _ ≤ 201 := by linarith
    have hb := polya_bound (by omega) hχ h201 T
    calc _ ≤ Real.sqrt q * (201 + 6) := hb
      _ = Real.sqrt q * ((207 / Real.log (Real.log 3)) * Real.log (Real.log 3)) := by
          field_simp; norm_num
      _ ≤ Real.sqrt q * (max (CB + 6) (207 / Real.log (Real.log 3)) * Real.log (Real.log q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (le_max_right _ _) hLL hc0.le (by positivity)) hsq
      _ = _ := by ring

end Vinogradov.PV
