import Mathlib
import Vinogradov.Riesz

/-!
# Elementary arithmetic for the primitive root bound

* `∑_{d ∣ N} μ(d)/d = φ(N)/N` and `N ≤ φ(N) τ(N)`;
* the divisor bound `τ(n) ≤ C_ε n^ε`;
* the principal character: `Re ∑_{n ≤ x} χ₀(n) Λ(n) (1 - n/x) ≥ ψ(x/2)/2 - log x`, and
  `ψ(x/2)/2 - log x ≥ x/10` for `x ≥ 10⁴`.
-/

namespace Vinogradov.Arith

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt LSeries.notation

/-- `∑_{d ∣ N} μ(d)/d = φ(N)/N`. -/
theorem sum_moebius_div {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, (μ d : ℝ) / d = (N.totient : ℝ) / N := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun n => (n.totient : ℝ)) (g := fun n => (n : ℝ))).1
    (fun n _ => by exact_mod_cast Nat.sum_totient n) N (Nat.pos_of_ne_zero hN)
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℝ) * (b : ℝ))] at h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [eq_div_iff hN', ← h, sum_mul]
  refine sum_congr rfl (fun d hd => ?_)
  have hdN := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdN hd0]
  field_simp

/-- `N ≤ φ(N) 2^{ω(N)}`. -/
theorem le_totient_mul_two_pow (N : ℕ) : N ≤ N.totient * 2 ^ N.primeFactors.card := by
  rcases Nat.eq_zero_or_pos N with rfl | _
  · simp
  have h := Nat.totient_mul_prod_primeFactors N
  have hpos : 0 < ∏ p ∈ N.primeFactors, (p - 1) :=
    prod_pos (fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
  have hle : ∏ p ∈ N.primeFactors, p ≤
      2 ^ N.primeFactors.card * ∏ p ∈ N.primeFactors, (p - 1) := by
    rw [← prod_const, ← prod_mul_distrib]
    apply prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h2 : N * ∏ p ∈ N.primeFactors, (p - 1) ≤
      (N.totient * 2 ^ N.primeFactors.card) * ∏ p ∈ N.primeFactors, (p - 1) := by
    rw [← h, mul_assoc]
    exact Nat.mul_le_mul_left _ hle
  exact Nat.le_of_mul_le_mul_right h2 hpos

/-- `2^{ω(N)} ≤ τ(N)`. -/
theorem two_pow_card_primeFactors_le {N : ℕ} (hN : N ≠ 0) :
    2 ^ N.primeFactors.card ≤ N.divisors.card := by
  rw [Nat.card_divisors hN, ← prod_const]
  apply prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun p hp => ?_)
  have : 0 < N.factorization p := by
    rw [← Nat.support_factorization] at hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  omega

/-- `1/τ(N) ≤ φ(N)/N`. -/
theorem inv_card_divisors_le {N : ℕ} (hN : N ≠ 0) :
    1 / (N.divisors.card : ℝ) ≤ (N.totient : ℝ) / N := by
  have h1 := le_totient_mul_two_pow N
  have h2 := two_pow_card_primeFactors_le hN
  have h3 : N ≤ N.totient * N.divisors.card :=
    h1.trans (Nat.mul_le_mul_left _ h2)
  have hτ : (0 : ℝ) < N.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [div_le_div_iff₀ hτ hN', one_mul]
  exact_mod_cast h3

/-- One prime factor in the divisor bound. -/
theorem prime_factor_bound {ε : ℝ} (hε : 0 < ε) (p a : ℕ) (hp : p.Prime) :
    ((a + 1 : ℕ) : ℝ) ≤
      (if p < ⌈(2 : ℝ) ^ (1 / ε)⌉₊ then 1 + 1 / (ε * Real.log 2) else 1) *
        (((p : ℝ) ^ a) ^ ε) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : ((p : ℝ) ^ a) ^ ε = ((p : ℝ) ^ ε) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0,
      Real.rpow_natCast]
  split_ifs with hP
  · have h2 : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp.two_le) hε.le
    have h3 : ((2 : ℝ) ^ ε) ^ a ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by positivity) h2 a
    have h4 : ((2 : ℝ) ^ ε) ^ a = Real.exp (a * ε * Real.log 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    have h5 := Real.add_one_le_exp (a * ε * Real.log 2)
    rw [hpow]
    have ha : (0 : ℝ) ≤ a := by positivity
    have h6 : ((a + 1 : ℕ) : ℝ) ≤ (1 + 1 / (ε * Real.log 2)) * (a * ε * Real.log 2 + 1) := by
      push_cast
      have hdl : 0 < ε * Real.log 2 := mul_pos hε hl2
      have : 1 / (ε * Real.log 2) * (a * ε * Real.log 2) = a := by field_simp
      nlinarith [div_pos one_pos hdl]
    calc ((a + 1 : ℕ) : ℝ) ≤ (1 + 1 / (ε * Real.log 2)) * (a * ε * Real.log 2 + 1) := h6
      _ ≤ (1 + 1 / (ε * Real.log 2)) * ((p : ℝ) ^ ε) ^ a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  · push Not at hP
    have hP' : (2 : ℝ) ^ (1 / ε) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hP)
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hP' hε.le
    rw [one_mul, hpow]
    calc ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast Nat.lt_two_pow_self
      _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h2 a

/-- **The divisor bound** `τ(n) ≤ C_ε n^ε`. -/
theorem card_divisors_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set P := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  set c : ℝ := 1 + 1 / (ε * Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 1 ≤ c := by
    have : 0 ≤ 1 / (ε * Real.log 2) := by positivity
    linarith
  refine ⟨c ^ P, one_le_pow₀ hc, fun n hn => ?_⟩
  set S := n.primeFactors
  have hτ : (n.divisors.card : ℝ) = ∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hn' : (n : ℝ) = ∏ p ∈ S, (p : ℝ) ^ n.factorization p := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact_mod_cast h.symm
  have hprod : ∏ p ∈ S, (if p < P then c else 1) ≤ c ^ P := by
    rw [prod_ite, prod_const_one, mul_one, prod_const]
    apply pow_le_pow_right₀ hc
    calc (S.filter (· < P)).card ≤ (range P).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter] at hp
          exact mem_range.mpr hp.2
      _ = P := card_range P
  rw [hτ]
  calc ∏ p ∈ S, ((n.factorization p + 1 : ℕ) : ℝ)
      ≤ ∏ p ∈ S, ((if p < P then c else 1) * (((p : ℝ) ^ n.factorization p) ^ ε)) := by
        apply prod_le_prod₀ (fun _ _ => by positivity)
        intro p hp
        exact prime_factor_bound hε p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ S, (if p < P then c else 1)) * (∏ p ∈ S, (p : ℝ) ^ n.factorization p) ^ ε := by
        rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    _ ≤ c ^ P * (n : ℝ) ^ ε := by
        rw [← hn']
        exact mul_le_mul_of_nonneg_right hprod (by positivity)

/-- The prime powers of `p` up to `x` contribute at most `log x` to `ψ(x)`. -/
theorem sum_vonMangoldt_dvd_le {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (p ∣ ·), Λ n ≤ Real.log x := by
  set K := Nat.log p ⌊x⌋₊
  have hfl : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx).ne'
  rw [← sum_filter_ne_zero]
  calc _ ≤ ∑ n ∈ (p ^ K).divisors, Λ n := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [mem_filter, mem_Ioc] at hn
          obtain ⟨⟨⟨_, hnx⟩, hpn⟩, hΛ⟩ := hn
          rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
          obtain ⟨r, k, hr, _, rfl⟩ := hΛ
          have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
          subst hpr
          rw [Nat.mem_divisors]
          exact ⟨pow_dvd_pow p (Nat.le_log_of_pow_le hp.one_lt hnx), pow_ne_zero _ hp.ne_zero⟩
        · intro n _ _
          exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log ((p ^ K : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log x := by
        have hpos : (0 : ℝ) < ((p ^ K : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos K
        apply Real.log_le_log hpos
        have h1 : p ^ K ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hfl
        calc ((p ^ K : ℕ) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
          _ ≤ x := Nat.floor_le (by linarith)

/-- The term of the principal character's Riesz sum. -/
theorem principal_term_re {p : ℕ} [Fact p.Prime] (x : ℝ) (n : ℕ) :
    ((↗(1 : DirichletCharacter ℂ p) * ↗Λ) n * (1 - (n : ℂ) / (x : ℂ))).re =
      Λ n * (1 - n / x) - (if p ∣ n then Λ n * (1 - n / x) else 0) := by
  have hre : ((Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))).re = Λ n * (1 - n / x) := by
    rw [show (1 : ℂ) - (n : ℂ) / (x : ℂ) = ((1 - n / x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  by_cases h : p ∣ n
  · have hnu : ¬ IsUnit (n : ZMod p) := by
      rw [(ZMod.natCast_eq_zero_iff n p).mpr h]
      exact not_isUnit_zero
    simp [h, MulChar.map_nonunit _ hnu]
  · have hu : IsUnit (n : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      exact h ((ZMod.natCast_eq_zero_iff n p).mp h0)
    simp only [Pi.mul_apply, MulChar.one_apply hu, one_mul, h, ite_false, sub_zero]
    exact hre

/-- **The principal character.** -/
theorem principal_re_ge {p : ℕ} [hp : Fact p.Prime] {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi (x / 2) / 2 - Real.log x ≤
      (Riesz.rieszSum (↗(1 : DirichletCharacter ℂ p) * ↗Λ) x).re := by
  have hx0 : 0 < x := by linarith
  unfold Riesz.rieszSum
  rw [Complex.re_sum]
  simp only [principal_term_re, sum_sub_distrib]
  have hw : ∀ n ∈ Ioc 0 ⌊x⌋₊, 0 ≤ 1 - (n : ℝ) / x ∧ 1 - (n : ℝ) / x ≤ 1 := by
    intro n hn
    have hn' : (n : ℝ) ≤ x := by
      have := (mem_Ioc.mp hn).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hx0.le)
    constructor
    · rw [sub_nonneg, div_le_one hx0]; exact hn'
    · have : 0 ≤ (n : ℝ) / x := by positivity
      linarith
  have hA : Chebyshev.psi (x / 2) / 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 - n / x) := by
    unfold Chebyshev.psi
    rw [sum_div]
    calc ∑ n ∈ Ioc 0 ⌊x / 2⌋₊, Λ n / 2 ≤ ∑ n ∈ Ioc 0 ⌊x / 2⌋₊, Λ n * (1 - n / x) := by
          apply sum_le_sum
          intro n hn
          have hn' : (n : ℝ) ≤ x / 2 :=
            (Nat.cast_le.mpr (mem_Ioc.mp hn).2).trans (Nat.floor_le (by positivity))
          have h1 : 1 / 2 ≤ 1 - (n : ℝ) / x := by
            have : (n : ℝ) / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
            linarith
          have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          nlinarith
      _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (1 - n / x) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [mem_Ioc] at hn ⊢
            exact ⟨hn.1, hn.2.trans (Nat.floor_le_floor (by linarith))⟩
          · intro n hn _
            exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n hn).1
  have hB : ∑ n ∈ Ioc 0 ⌊x⌋₊, (if p ∣ n then Λ n * (1 - n / x) else 0) ≤ Real.log x := by
    rw [← sum_filter]
    refine le_trans ?_ (sum_vonMangoldt_dvd_le hp.out hx)
    apply sum_le_sum
    intro n hn
    have hn2 := (hw n (mem_filter.mp hn).1).2
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    nlinarith
  linarith

/-- `ψ(x/2)/2 - log x ≥ x/10` for `x ≥ 10⁴`. -/
theorem psi_half_ge {x : ℝ} (hx : 10000 ≤ x) :
    x / 10 ≤ Chebyshev.psi (x / 2) / 2 - Real.log x := by
  have hx0 : 0 < x := by linarith
  have hpsi := Chebyshev.psi_ge' (x := x / 2) (by positivity)
  have hl2 := Real.log_two_gt_d9
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs100 : 100 ≤ Real.sqrt x := by
    rw [show (100 : ℝ) = Real.sqrt (100 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hlog2 : Real.log (x / 2 + 2) ≤ Real.log x :=
    Real.log_le_log (by positivity) (by linarith)
  nlinarith

end Vinogradov.Arith
