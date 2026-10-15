import Vinogradov.PV.Main

/-!
# The range of `x` in which `∑_{n ≤ x} χ(n) = o(x)`

For a nonprincipal character `χ` modulo `q ≥ 3` and `x ≥ 2`,
`‖∑_{n ≤ x} χ(n)‖ ≤ C x (log log q / log x + 1 / log q)`.
Integers `n ≤ x` with a prime factor above `Y = ⌈log q⌉^{40}` are counted through the prime sums
of the zero-free half-plane (`twisted_prime_sum` at `θ = 0`); the integers without one are at most
`x (1 + 2 log Y + 2 log 4) / log x` by Chebyshev's argument.
-/

namespace Vinogradov.PV

open Finset Complex

/-- **Integers with a large prime factor.** For `χ` nonprincipal modulo `q` and `2 ≤ Y`,
`‖∑_{n ≤ t, gpf n > Y} χ(n)‖ ≤ C log (q + 2) t / (Y^{1/20} log Y)`. -/
theorem nonsmooth_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ Y t : ℕ, 2 ≤ Y →
        ‖∑ n ∈ Ioc 0 t with Y < gpf n, (χ n : ℂ)‖ ≤
          C * Real.log (q + 2) * t / ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) := by
  obtain ⟨C, hC, hCb⟩ := twisted_prime_sum
  refine ⟨40 * C, by positivity, ?_⟩
  intro q _ χ hχ Y t hY
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLq : 0 ≤ Real.log (q + 2) := Real.log_nonneg (by linarith)
  set K : ℝ := 2 * C * Real.log (q + 2) / Real.log Y with hK
  have hK0 : 0 ≤ K := by positivity
  rw [sum_gpf]
  have hinner : ∀ m ∈ Ioc 0 t,
      ‖∑ p ∈ Ioc (max Y (gpf m - 1)) (t / m) with p.Prime, (χ (p * m : ℕ) : ℂ)‖ ≤
        if m ≤ t / Y then K * (((t : ℝ) / m) ^ (19 / 20 : ℝ)) else 0 := by
    intro m hm
    obtain ⟨hm0, hmt⟩ := mem_Ioc.mp hm
    have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
    set A := max Y (gpf m - 1) with hA
    set B := t / m with hB
    by_cases hAB : A ≤ B
    · have hYB : Y ≤ B := (le_max_left _ _).trans hAB
      have hmY : m ≤ t / Y := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        have := (Nat.le_div_iff_mul_le hm0).mp hYB
        linarith [mul_comm Y m]
      simp only [hmY, ↓reduceIte]
      have hrew : ∑ p ∈ Ioc A B with p.Prime, (χ (p * m : ℕ) : ℂ) =
          χ m * ∑ p ∈ Ioc A B with p.Prime, (χ p : ℂ) * e (p * 0) := by
        rw [mul_sum]
        refine sum_congr rfl fun p _ => ?_
        rw [mul_zero, e_zero, mul_one, Nat.cast_mul, map_mul, mul_comm]
      rw [hrew, norm_mul]
      have hχm : ‖(χ m : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ m
      have hA2 : 2 ≤ A := hY.trans (le_max_left _ _)
      have h := hCb q χ hχ A B hA2 hAB 0
      have hBt : (B : ℝ) ≤ t / m := by
        rw [hB, le_div_iff₀ hm0']
        exact_mod_cast Nat.div_mul_le_self t m
      have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      have hlA : Real.log Y ≤ Real.log A :=
        Real.log_le_log (by linarith) (by exact_mod_cast le_max_left Y (gpf m - 1))
      have hpowB : (B : ℝ) ^ (19 / 20 : ℝ) ≤ ((t : ℝ) / m) ^ (19 / 20 : ℝ) :=
        Real.rpow_le_rpow hB0 hBt (by norm_num)
      calc ‖(χ m : ℂ)‖ * _ ≤ 1 * (C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (q + 2) *
            (2 + 2 * Real.pi * |(0 : ℝ)| * B) / Real.log A) :=
            mul_le_mul hχm h (norm_nonneg _) zero_le_one
        _ = C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (q + 2) * 2 / Real.log A := by
            rw [abs_zero]; ring
        _ ≤ C * ((t : ℝ) / m) ^ (19 / 20 : ℝ) * Real.log (q + 2) * 2 / Real.log Y := by
            gcongr
        _ = K * (((t : ℝ) / m) ^ (19 / 20 : ℝ)) := by rw [hK]; ring
    · rw [not_le] at hAB
      rw [Ioc_eq_empty (by omega), filter_empty, sum_empty, norm_zero]
      split_ifs <;> [positivity; exact le_rfl]
  calc _ ≤ ∑ m ∈ Ioc 0 t,
        ‖∑ p ∈ Ioc (max Y (gpf m - 1)) (t / m) with p.Prime, (χ (p * m : ℕ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 t, (if m ≤ t / Y then K * (((t : ℝ) / m) ^ (19 / 20 : ℝ)) else 0) :=
        sum_le_sum hinner
    _ = ∑ m ∈ Ioc 0 (t / Y), K * (((t : ℝ) / m) ^ (19 / 20 : ℝ)) := by
        rw [← sum_filter]
        congr 1
        ext m
        simp only [mem_filter, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (Nat.div_le_self t Y)⟩, h2⟩
    _ = K * (t : ℝ) ^ (19 / 20 : ℝ) * ∑ m ∈ Ioc 0 (t / Y), ((m : ℝ) ^ (19 / 20 : ℝ))⁻¹ := by
        rw [mul_assoc, mul_sum, mul_sum]
        refine sum_congr rfl fun m hm => ?_
        rw [Real.div_rpow (Nat.cast_nonneg t) (Nat.cast_nonneg m), div_eq_mul_inv]
    _ ≤ K * (t : ℝ) ^ (19 / 20 : ℝ) * (20 * ((t / Y : ℕ) : ℝ) ^ (1 / 20 : ℝ)) := by
        gcongr
        exact sum_rpow_le _
    _ ≤ K * (t : ℝ) ^ (19 / 20 : ℝ) * (20 * ((t : ℝ) / Y) ^ (1 / 20 : ℝ)) := by
        gcongr
        exact Nat.cast_div_le
    _ = 20 * K * ((t : ℝ) ^ (19 / 20 : ℝ) * (t : ℝ) ^ (1 / 20 : ℝ)) /
          (Y : ℝ) ^ (1 / 20 : ℝ) := by
        rw [Real.div_rpow (Nat.cast_nonneg t) (by linarith)]
        ring
    _ = 20 * K * t / (Y : ℝ) ^ (1 / 20 : ℝ) := by
        rw [← Real.rpow_add' (Nat.cast_nonneg t) (by norm_num)]; norm_num
    _ = _ := by
        have hYp : 0 < (Y : ℝ) ^ (1 / 20 : ℝ) := by positivity
        rw [hK]; field_simp; ring

/-- `log x! = ∑_{n ≤ x} log n`. -/
theorem log_factorial_eq (x : ℕ) :
    Real.log (x.factorial : ℕ) = ∑ n ∈ Ioc 0 x, Real.log n := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le x), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos x).ne'), add_comm]

/-- `∑_{n ≤ x} log (x/n) ≤ x`. -/
theorem sum_log_div_le (x : ℕ) : ∑ n ∈ Ioc 0 x, Real.log ((x : ℝ) / n) ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hf : (0 : ℝ) < (x.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos x
  have h1 : ∑ n ∈ Ioc 0 x, Real.log ((x : ℝ) / n) =
      x * Real.log x - Real.log (x.factorial : ℕ) := by
    rw [log_factorial_eq]
    have : ∑ n ∈ Ioc 0 x, Real.log ((x : ℝ) / n) =
        ∑ n ∈ Ioc 0 x, (Real.log x - Real.log n) := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      rw [Real.log_div hx0.ne' hn0.ne']
    rw [this, sum_sub_distrib, sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
  have h2 : Real.log ((x : ℝ) ^ x / (x.factorial : ℕ)) ≤ x := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    exact Real.pow_div_factorial_le_exp (x : ℝ) hx0.le x
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow] at h2
  rw [h1]; exact h2

/-- `∑_{n ≤ x} v_p(n) = v_p(x!)`. -/
theorem sum_factorization_eq (x p : ℕ) :
    ∑ n ∈ Ioc 0 x, n.factorization p = (x.factorial).factorization p := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le x), ih, Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero x) (Nat.factorial_pos x).ne', Finsupp.add_apply,
      add_comm]

/-- **Chebyshev's bound for smooth numbers.** The number `Ψ(x, Y)` of `n ≤ x` with no prime
factor above `Y` satisfies `Ψ(x, Y) log x ≤ x (1 + 2 log Y + 2 log 4)`. -/
theorem psi_log_le (x Y : ℕ) :
    (((Ioc 0 x).filter (fun n => gpf n ≤ Y)).card : ℝ) * Real.log x ≤
      x * (1 + 2 * (Real.log Y + Real.log 4)) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  set S := (Ioc 0 x).filter (fun n => gpf n ≤ Y) with hS
  set P := (Ioc 0 Y).filter Nat.Prime with hP
  -- `log n` through the primes up to `Y`
  have hlogn : ∀ n ∈ S, Real.log n = ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p := by
    intro n hn
    obtain ⟨hn, hgn⟩ := mem_filter.mp hn
    have hsupp : n.factorization.support ⊆ P := by
      intro p hp
      rw [Nat.support_factorization] at hp
      have hpY : p ≤ Y := (le_gpf hp).trans hgn
      have hpp := Nat.prime_of_mem_primeFactors hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, hpY⟩, hpp⟩
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ hsupp]
    intro p _; simp
  have hsplit : (S.card : ℝ) * Real.log x =
      ∑ n ∈ S, Real.log ((x : ℝ) / n) + ∑ n ∈ S, Real.log n := by
    rw [← sum_add_distrib, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).1
    rw [Real.log_div hx0.ne' hn0.ne']; ring
  -- the first sum
  have hA : ∑ n ∈ S, Real.log ((x : ℝ) / n) ≤ x := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_) (sum_log_div_le x)
    intro n hn _
    obtain ⟨hn0, hnx⟩ := mem_Ioc.mp hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    exact Real.log_nonneg (by rw [le_div_iff₀ hn0']; simpa using (by exact_mod_cast hnx))
  -- the second sum
  have hB : ∑ n ∈ S, Real.log n ≤ 2 * x * (Real.log Y + Real.log 4) := by
    calc ∑ n ∈ S, Real.log n = ∑ n ∈ S, ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p :=
          sum_congr rfl hlogn
      _ ≤ ∑ n ∈ Ioc 0 x, ∑ p ∈ P, (n.factorization p : ℝ) * Real.log p := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => ?_
          exact sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
      _ = ∑ p ∈ P, ((x.factorial).factorization p : ℝ) * Real.log p := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [← sum_mul, ← sum_factorization_eq]; push_cast; rfl
      _ ≤ ∑ p ∈ P, 2 * x * (Real.log p / p) := by
          refine sum_le_sum fun p hp => ?_
          have hpp : p.Prime := (mem_filter.mp hp).2
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
          have h1 : ((x.factorial).factorization p : ℝ) ≤ ((x / (p - 1) : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorization_factorial_le_div_pred hpp x
          have h2 : ((x / (p - 1) : ℕ) : ℝ) ≤ (x : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
          have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
            rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
          have h4 : (x : ℝ) / ((p : ℝ) - 1) ≤ 2 * x / p := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith
          have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          calc ((x.factorial).factorization p : ℝ) * Real.log p ≤ (2 * x / p) * Real.log p :=
                mul_le_mul_of_nonneg_right (by rw [h3] at h2; linarith) hlogp
            _ = 2 * x * (Real.log p / p) := by ring
      _ = 2 * x * ∑ p ∈ P, Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * x * (Real.log Y + Real.log 4) := by
          gcongr
          exact mertens_first Y
  rw [hsplit]
  linarith

/-- `log log q ≥ log log 3 > 0` for `q ≥ 3`. -/
theorem log_log_ge {q : ℝ} (hq : 3 ≤ q) : Real.log (Real.log 3) ≤ Real.log (Real.log q) :=
  Real.log_le_log (by linarith [one_lt_log_three]) (Real.log_le_log (by norm_num) hq)

/-- The parameter `Y = ⌈log q⌉^{40}` and the facts about it used below. -/
theorem param_facts {q : ℕ} (hq3 : 3 ≤ q) :
    1 < Real.log q ∧ 2 ≤ ⌈Real.log q⌉₊ ∧ Real.log q ≤ ⌈Real.log q⌉₊ ∧
      (⌈Real.log q⌉₊ : ℝ) ≤ 2 * Real.log q ∧ 2 ≤ ⌈Real.log q⌉₊ ^ 40 ∧
      ((⌈Real.log q⌉₊ ^ 40 : ℕ) : ℝ) ^ (1 / 20 : ℝ) = (⌈Real.log q⌉₊ : ℝ) ^ 2 ∧
      Real.log ((⌈Real.log q⌉₊ ^ 40 : ℕ) : ℝ) = 40 * Real.log ⌈Real.log q⌉₊ ∧
      Real.log (q + 2) ≤ 2 * Real.log q := by
  set L := Real.log q with hLdef
  set M := ⌈L⌉₊ with hMdef
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hL1 : 1 < L := lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hq)
  have hL0 : 0 < L := by linarith
  have hML : L ≤ M := Nat.le_ceil L
  have hML1 : (M : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0.le
  have hM2 : 2 ≤ M := by
    have : 1 < M := Nat.lt_ceil.mpr (by exact_mod_cast hL1)
    omega
  have hY2 : 2 ≤ M ^ 40 :=
    calc 2 ≤ M := hM2
      _ ≤ M ^ 40 := Nat.le_self_pow (by norm_num) M
  have hYc : ((M ^ 40 : ℕ) : ℝ) = (M : ℝ) ^ 40 := Nat.cast_pow M 40
  refine ⟨hL1, hM2, hML, by linarith, hY2, ?_, ?_, ?_⟩
  · rw [hYc, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg M)]
    norm_num
  · rw [hYc, Real.log_pow]; norm_num
  · have h2 : Real.log ((q : ℝ) ^ 2) = 2 * L := by rw [Real.log_pow, hLdef]; push_cast; ring
    rw [← h2]
    exact Real.log_le_log (by linarith) (by nlinarith)

/-- **Smooth numbers and a remainder.** There is an absolute constant `C` such that for every
nonprincipal character `χ` modulo `q ≥ 3` and every `x`,
`‖∑_{n ≤ x} χ(n)‖ ≤ Ψ(x, ⌈log q⌉^{40}) + C x / log q`. -/
theorem character_sum_psi :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ,
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          (((Ioc 0 x).filter (fun n => gpf n ≤ ⌈Real.log q⌉₊ ^ 40)).card : ℝ) +
            C * x / Real.log q := by
  obtain ⟨C1, hC1, hR⟩ := nonsmooth_sum
  refine ⟨2 * C1, by positivity, ?_⟩
  intro q _ χ hχ hq3 x
  obtain ⟨hL1, hM2, hML, -, hY2, hY20, hlogY, hlq⟩ := param_facts hq3
  set L := Real.log q with hLdef
  set M := ⌈L⌉₊ with hM
  set Y := M ^ 40 with hYdef
  have hL0 : 0 < L := by linarith
  have hlogY1 : 1 ≤ Real.log Y := by
    rw [hlogY]
    have hM2' : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    have : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2'
    have := Real.log_two_gt_d9; norm_num at this; linarith
  have hsplit : ∑ n ∈ Ioc 0 x, (χ n : ℂ) =
      ∑ n ∈ Ioc 0 x with gpf n ≤ Y, (χ n : ℂ) + ∑ n ∈ Ioc 0 x with Y < gpf n, (χ n : ℂ) := by
    rw [← sum_filter_add_sum_filter_not (Ioc 0 x) (fun n => gpf n ≤ Y)]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext n; simp [not_le]
  have hsmooth : ‖∑ n ∈ Ioc 0 x with gpf n ≤ Y, (χ n : ℂ)‖ ≤
      (((Ioc 0 x).filter (fun n => gpf n ≤ Y)).card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ n
  have hrough : ‖∑ n ∈ Ioc 0 x with Y < gpf n, (χ n : ℂ)‖ ≤ 2 * C1 * x / L := by
    have h1 := hR q χ hχ Y x hY2
    have hM2L : L ^ 2 ≤ (M : ℝ) ^ 2 := by gcongr
    calc _ ≤ C1 * Real.log (q + 2) * x / ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) := h1
      _ ≤ C1 * (2 * L) * x / (L ^ 2 * 1) := by
          rw [hY20]
          gcongr
      _ = 2 * C1 * x / L := by field_simp
  rw [hsplit]
  calc _ ≤ ‖∑ n ∈ Ioc 0 x with gpf n ≤ Y, (χ n : ℂ)‖ +
        ‖∑ n ∈ Ioc 0 x with Y < gpf n, (χ n : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hsmooth hrough

/-- **The range of `x` in which `∑_{n ≤ x} χ(n) = o(x)`.** There is an absolute constant `C`
such that for every nonprincipal character `χ` modulo `q ≥ 3` and every `x ≥ 2`,
`‖∑_{n ≤ x} χ(n)‖ ≤ C x (log log q / log x + 1 / log q)`. -/
theorem character_sum_range :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
      ∀ x : ℕ, 2 ≤ x →
        ‖∑ n ∈ Ioc 0 x, (χ n : ℂ)‖ ≤
          C * x * (Real.log (Real.log q) / Real.log x + 1 / Real.log q) := by
  obtain ⟨C2, hC2, hP⟩ := character_sum_psi
  set c := Real.log (Real.log 3) with hc
  have hc0 : 0 < c := Real.log_pos one_lt_log_three
  refine ⟨85 / c + 80 + C2, by positivity, ?_⟩
  intro q _ χ hχ hq3 x hx
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h5 := hP q χ hχ hq3 x
  obtain ⟨hL1, hM2, -, hM2L, -, -, hlogY, -⟩ := param_facts hq3
  set L := Real.log q with hLdef
  set M := ⌈L⌉₊ with hM
  set Y := M ^ 40 with hYdef
  have hL0 : 0 < L := by linarith
  set LL := Real.log L with hLL
  have hcLL : c ≤ LL := log_log_ge hq
  have hLL0 : 0 < LL := by linarith
  have hM2' : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hlogM : Real.log M ≤ Real.log 2 + LL := by
    rw [← Real.log_mul (by norm_num) hL0.ne']
    exact Real.log_le_log (by linarith) hM2L
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hlogM0 : 0 < Real.log M := Real.log_pos (by linarith)
  have h2 := psi_log_le x Y
  have h3 : 1 + 2 * (Real.log Y + Real.log 4) ≤ (85 / c + 80) * LL := by
    have h85 : 85 ≤ 85 / c * LL := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]; nlinarith
    rw [hlogY]; nlinarith
  have h4 : (((Ioc 0 x).filter (fun n => gpf n ≤ Y)).card : ℝ) ≤
      (85 / c + 80) * x * (LL / Real.log x) := by
    rw [mul_div_assoc', le_div_iff₀ hlogx]
    calc _ ≤ x * (1 + 2 * (Real.log Y + Real.log 4)) := h2
      _ ≤ x * ((85 / c + 80) * LL) := by gcongr
      _ = _ := by ring
  calc _ ≤ _ := h5
    _ ≤ (85 / c + 80) * x * (LL / Real.log x) + C2 * x * (1 / L) := by
        rw [mul_one_div]; exact add_le_add h4 le_rfl
    _ ≤ (85 / c + 80 + C2) * x * (LL / Real.log x + 1 / L) := by
        have ha : 0 ≤ LL / Real.log x := by positivity
        have hb : 0 ≤ 1 / L := by positivity
        have hxc : 0 ≤ (x : ℝ) := hx0.le
        nlinarith [mul_nonneg (mul_nonneg hxc ha) hC2.le,
          mul_nonneg (mul_nonneg hxc hb) (by positivity : (0 : ℝ) ≤ 85 / c + 80)]

end Vinogradov.PV
