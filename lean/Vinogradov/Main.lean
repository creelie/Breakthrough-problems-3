import Mathlib
import Vinogradov.Analytic
import Vinogradov.Characters
import Vinogradov.Arith

/-!
# The least prime primitive root under a zero-free half-plane

If no Dirichlet L-function of a nonprincipal character vanishes for `re s > 7/8`, then for every
`η > 0` there is `C` such that every prime `p` has a prime primitive root
`ℓ ≤ C (τ(p-1)² log (p + 2))^{8+η}`. Consequently `ℓ ≤ C_ε p^ε` (Vinogradov's conjecture on the
least primitive root), and every prime `p ≥ p₀` has a prime primitive root `ℓ < p`.
-/

namespace Vinogradov.Main

open Finset Complex
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt LSeries.notation

/-- No `L(s, χ)` with `χ` nonprincipal vanishes on `re s > 7/8`. -/
def ZeroFree : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ z : ℂ, 7 / 8 < z.re → DirichletCharacter.LFunction χ z ≠ 0

section prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- A nonzero Riesz sum over primitive roots produces a prime primitive root `ℓ ≤ x`. -/
theorem exists_prime_of_genSum_ne_zero {x : ℝ} (h : Characters.genSum p x ≠ 0) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : ℝ) ≤ x ∧ orderOf (ℓ : ZMod p) = p - 1 := by
  by_contra hne
  push Not at hne
  apply h
  unfold Characters.genSum Riesz.rieszSum
  apply sum_eq_zero
  intro n hn
  by_cases hord : orderOf (n : ZMod p) = p - 1
  · by_cases hΛ : Λ n = 0
    · simp [hΛ]
    · exfalso
      rw [← ne_eq, ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
      obtain ⟨ℓ, k, hℓ, hk, rfl⟩ := hΛ
      have h2 : ℓ ^ k ≤ ⌊x⌋₊ := (mem_Ioc.mp hn).2
      have h3 : 0 < ⌊x⌋₊ := lt_of_lt_of_le (pow_pos hℓ.pos k) h2
      have hx1 : 1 ≤ x := Nat.floor_pos.mp h3
      refine hne ℓ hℓ ?_ ?_
      · calc (ℓ : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.le_self_pow hk.ne' ℓ).trans h2
          _ ≤ x := Nat.floor_le (by linarith)
      · push_cast at hord
        have hN : p - 1 ≠ 0 := (Characters.sub_one_pos (p := p)).ne'
        have hunit : IsUnit ((ℓ : ZMod p) ^ k) :=
          IsUnit.of_pow_eq_one (by rw [← hord]; exact pow_orderOf_eq_one _) hN
        have hu : IsUnit (ℓ : ZMod p) := (isUnit_pow_iff hk.ne').mp hunit
        apply Nat.dvd_antisymm
        · have he : orderOf (ℓ : ZMod p) = orderOf hu.unit := by
            rw [← orderOf_units, IsUnit.unit_spec]
          rw [he]
          exact ZMod.orderOf_units_dvd_card_sub_one hu.unit
        · rw [← hord]
          exact orderOf_pow_dvd k
  · simp [hord]

/-- Splitting off the principal character. -/
theorem genSum_decomp (S : Characters.Setup p) (x : ℝ) :
    Characters.genSum p x =
      (∑ d ∈ (p - 1).divisors, (μ d : ℂ) / d) *
          Riesz.rieszSum (↗(1 : DirichletCharacter ℂ p) * ↗Λ) x +
        ∑ d ∈ (p - 1).divisors, ((μ d : ℂ) / d) *
          ∑ m ∈ Ico 1 d, Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x := by
  rw [Characters.genSum_eq S, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl (fun d hd => ?_)
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hd0]
  simp only [zero_mul, pow_zero]
  ring

/-- The nonprincipal part is at most `τ(p-1) B`. -/
theorem error_le (S : Characters.Setup p) {x B : ℝ} (hB : 0 ≤ B)
    (hχ : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤ B) :
    ‖∑ d ∈ (p - 1).divisors, ((μ d : ℂ) / d) *
        ∑ m ∈ Ico 1 d, Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x‖ ≤
      (p - 1).divisors.card * B := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ (p - 1).divisors, ‖((μ d : ℂ) / d) *
        ∑ m ∈ Ico 1 d, Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x‖
      ≤ ∑ d ∈ (p - 1).divisors, B := by
        apply sum_le_sum
        intro d hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
        have hinner : ‖∑ m ∈ Ico 1 d,
            Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x‖ ≤ (d : ℝ) * B := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ m ∈ Ico 1 d, ‖Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x‖
              ≤ ∑ m ∈ Ico 1 d, B := by
                apply sum_le_sum
                intro m hm
                obtain ⟨hm1, hmd⟩ := mem_Ico.mp hm
                exact hχ _ (Characters.pow_ne_one S hd hm1 hmd)
            _ = ((d - 1 : ℕ) : ℝ) * B := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
            _ ≤ (d : ℝ) * B := by
                apply mul_le_mul_of_nonneg_right _ hB
                exact_mod_cast Nat.sub_le d 1
        have hμ : ‖(μ d : ℂ) / d‖ ≤ 1 / d := by
          rw [norm_div, Complex.norm_natCast]
          apply div_le_div_of_nonneg_right _ hd0.le
          have h := ArithmeticFunction.abs_moebius_le_one (n := d)
          rw [show ‖(μ d : ℂ)‖ = |(μ d : ℝ)| by
            rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]]
          exact_mod_cast h
        rw [norm_mul]
        calc ‖(μ d : ℂ) / d‖ * ‖∑ m ∈ Ico 1 d,
              Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x‖
            ≤ 1 / d * ((d : ℝ) * B) := mul_le_mul hμ hinner (norm_nonneg _) (by positivity)
          _ = B := by field_simp
    _ = (p - 1).divisors.card * B := by rw [sum_const, nsmul_eq_mul]

/-- **Lower bound for the primitive-root sum.** -/
theorem genSum_norm_ge {x B : ℝ} (hx : 10000 ≤ x) (hB : 0 ≤ B)
    (hχ : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤ B) :
    x / 10 / (p - 1).divisors.card - (p - 1).divisors.card * B ≤
      ‖Characters.genSum p x‖ := by
  obtain ⟨S⟩ := Characters.exists_setup (p := p)
  have hN : p - 1 ≠ 0 := (Characters.sub_one_pos (p := p)).ne'
  set τ : ℝ := ((p - 1).divisors.card : ℝ)
  have hτ : 0 < τ :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hN))
  set c : ℝ := ((p - 1).totient : ℝ) / (p - 1 : ℕ)
  have hc : (∑ d ∈ (p - 1).divisors, (μ d : ℂ) / d) = (c : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (Arith.sum_moebius_div hN)
    push_cast at h
    rw [h]
    simp [c]
  have hc0 : 0 ≤ c := by positivity
  have hcτ : 1 / τ ≤ c := Arith.inv_card_divisors_le hN
  set S1 := Riesz.rieszSum (↗(1 : DirichletCharacter ℂ p) * ↗Λ) x
  set E := ∑ d ∈ (p - 1).divisors, ((μ d : ℂ) / d) *
    ∑ m ∈ Ico 1 d, Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x
  have hdec : Characters.genSum p x = (c : ℂ) * S1 + E := by
    rw [genSum_decomp S x, hc]
  have hE := error_le S hB hχ
  have hS1 : x / 10 ≤ S1.re :=
    (Arith.psi_half_ge hx).trans (Arith.principal_re_ge (p := p) (by linarith))
  have h1 : ‖(c : ℂ) * S1‖ ≤ ‖Characters.genSum p x‖ + ‖E‖ := by
    have : (c : ℂ) * S1 = Characters.genSum p x - E := by rw [hdec]; ring
    rw [this]
    exact norm_sub_le _ _
  have h2 : c * (x / 10) ≤ ‖(c : ℂ) * S1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hS1.trans (Complex.re_le_norm S1)) hc0
  have h3 : x / 10 / τ ≤ c * (x / 10) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hcτ (by linarith)
  linarith

end prime

/-- **The least prime primitive root.** Under `ZeroFree`, for every `η > 0` there is `C` with
`g*(p) ≤ C (τ(p-1)² log (p + 2))^{8+η}` for every prime `p`. -/
theorem least_prime_primitive_root_bound (hZ : ZeroFree) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)) ^ (8 + η) := by
  set e : ℝ := η / (2000 * (8 + η))
  have he : 0 < e := by positivity
  have he' : e < 1 / 1000 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨K, hK, hKb⟩ := Analytic.riesz_character_bound he he'
  set K' := max K 1
  have hK' : 1 ≤ K' := le_max_right K 1
  set σ0 : ℝ := 7 / 8 + 8 * e
  set β : ℝ := 1 / 8 - 8 * e
  have hσβ : σ0 + β = 1 := by ring
  have hβ0 : 0 < β := by
    have : 8 * e < 1 / 8 := by linarith
    simp only [β]
    linarith
  have hβ : 1 ≤ (8 + η) * β := by
    have h8 : (8 + η) * (8 * e) = η / 250 := by
      simp only [e]
      field_simp
      ring
    have : (8 + η) * β = (8 + η) / 8 - η / 250 := by
      simp only [β]
      rw [mul_sub, h8]
      ring
    rw [this]
    linarith
  set C0 : ℝ := max 10000 ((20 * K') ^ (8 + η))
  have hC0 : 10000 ≤ C0 := le_max_left _ _
  refine ⟨C0, by linarith, fun p hp => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hN : p - 1 ≠ 0 := (Characters.sub_one_pos (p := p)).ne'
  set τ : ℝ := ((p - 1).divisors.card : ℝ)
  have hτ1 : 1 ≤ τ :=
    Nat.one_le_cast.mpr (Finset.card_pos.mpr (Nat.nonempty_divisors.mpr hN))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog1 : 1 ≤ Real.log (p + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := τ ^ 2 * Real.log (p + 2)
  have hY : 1 ≤ Y := by
    have : 1 ≤ τ ^ 2 := one_le_pow₀ hτ1
    nlinarith
  set x : ℝ := C0 * Y ^ (8 + η)
  have hYp : 1 ≤ Y ^ (8 + η) := Real.one_le_rpow hY (by linarith)
  have hx : 10000 ≤ x := by nlinarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set B : ℝ := K' * x ^ σ0 * Real.log (p + 2)
  have hB : 0 ≤ B := by positivity
  have hχ : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖Riesz.rieszSum (↗χ * ↗Λ) x‖ ≤ B := by
    intro χ hχ
    have h := hKb p χ hχ (7 / 8) (by norm_num) (by norm_num)
      (fun z hz => hZ p χ hχ z (by linarith)) x hx1
    calc _ ≤ K * x ^ (7 / 8 + 8 * e) * Real.log (p + 2) := h
      _ ≤ B := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left K 1) (by positivity)
  -- the main inequality `τ² B < x / 10`
  have hxβ : 20 * K' * Y ≤ x ^ β := by
    have h1 : x ^ β = C0 ^ β * Y ^ ((8 + η) * β) := by
      simp only [x]
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
    have h2 : 20 * K' ≤ C0 ^ β := by
      calc 20 * K' = (20 * K') ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (20 * K') ^ ((8 + η) * β) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
        _ = ((20 * K') ^ (8 + η)) ^ β := by rw [Real.rpow_mul (by positivity)]
        _ ≤ C0 ^ β := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hβ0.le
    have h3 : Y ≤ Y ^ ((8 + η) * β) := by
      calc Y = Y ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ Y ^ ((8 + η) * β) := Real.rpow_le_rpow_of_exponent_le hY hβ
    rw [h1]
    exact mul_le_mul h2 h3 (by linarith) (by positivity)
  have hxs : 0 < x ^ σ0 := by positivity
  have hmain : τ ^ 2 * B < x / 10 := by
    have : τ ^ 2 * B = K' * Y * x ^ σ0 := by simp only [B, Y]; ring
    rw [this]
    have hKY : 0 < K' * Y := by positivity
    calc K' * Y * x ^ σ0 < 2 * (K' * Y) * x ^ σ0 := by nlinarith
      _ = (20 * K' * Y) * x ^ σ0 / 10 := by ring
      _ ≤ x ^ β * x ^ σ0 / 10 := by gcongr
      _ = x / 10 := by rw [← Real.rpow_add hx0, add_comm, hσβ, Real.rpow_one]
  have hge := genSum_norm_ge (p := p) hx hB hχ
  have hpos : 0 < ‖Characters.genSum p x‖ := by
    have hτ0 : 0 < τ := by linarith
    have : τ * B < x / 10 / τ := by
      rw [lt_div_iff₀ hτ0]
      nlinarith
    linarith
  obtain ⟨ℓ, hℓ, hℓx, hord⟩ := exists_prime_of_genSum_ne_zero (norm_pos_iff.mp hpos)
  exact ⟨ℓ, hℓ, hord, hℓx⟩

/-- **Vinogradov's conjecture for the least prime primitive root.** Under `ZeroFree`, for every
`ε > 0` there is `C` such that every prime `p` has a prime primitive root `ℓ ≤ C p^ε`. -/
theorem least_prime_primitive_root_le_rpow (hZ : ZeroFree) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε := by
  obtain ⟨C0, hC0, h0⟩ := least_prime_primitive_root_bound hZ (η := 1) one_pos
  set ν : ℝ := ε / 27 with hνdef
  have hν : 0 < ν := by positivity
  obtain ⟨C1, hC1, hdiv⟩ := Arith.card_divisors_le hν
  set C2 : ℝ := 3 ^ ν / ν with hC2
  set C3 : ℝ := C1 ^ 2 * C2 with hC3
  have hC2p : 0 < C2 := by positivity
  have hC3p : 0 < C3 := by positivity
  refine ⟨C0 * C3 ^ ((8 : ℝ) + 1), by positivity, fun p hp => ?_⟩
  obtain ⟨ℓ, hℓ, hord, hle⟩ := h0 p hp
  refine ⟨ℓ, hℓ, hord, hle.trans ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hτ : ((p - 1).divisors.card : ℝ) ≤ C1 * (p : ℝ) ^ ν := by
    have h := hdiv (p - 1) (Nat.sub_pos_of_lt hp.one_lt).ne'
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    apply Real.rpow_le_rpow (by positivity) _ hν.le
    exact_mod_cast Nat.sub_le p 1
  have hlog : Real.log (p + 2) ≤ C2 * (p : ℝ) ^ ν := by
    have h := Real.log_le_rpow_div (x := (p : ℝ) + 2) (by positivity) hν
    calc Real.log (p + 2) ≤ ((p : ℝ) + 2) ^ ν / ν := h
      _ ≤ (3 * (p : ℝ)) ^ ν / ν := by gcongr; linarith
      _ = C2 * (p : ℝ) ^ ν := by
        rw [Real.mul_rpow (by norm_num) hp0.le, hC2]
        ring
  have hlog0 : 0 ≤ Real.log (p + 2) := Real.log_nonneg (by linarith)
  have hY : ((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2) ≤ C3 * (p : ℝ) ^ (3 * ν) := by
    have h3 : (p : ℝ) ^ (3 * ν) = ((p : ℝ) ^ ν) ^ 2 * (p : ℝ) ^ ν := by
      rw [show 3 * ν = ν * 2 + ν by ring, Real.rpow_add hp0, Real.rpow_mul hp0.le]
      norm_num
    rw [h3]
    calc ((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)
        ≤ (C1 * (p : ℝ) ^ ν) ^ 2 * (C2 * (p : ℝ) ^ ν) := by gcongr
      _ = C3 * (((p : ℝ) ^ ν) ^ 2 * (p : ℝ) ^ ν) := by rw [hC3]; ring
  calc C0 * (((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)) ^ ((8 : ℝ) + 1)
      ≤ C0 * (C3 * (p : ℝ) ^ (3 * ν)) ^ ((8 : ℝ) + 1) := by gcongr
    _ = C0 * C3 ^ ((8 : ℝ) + 1) * (p : ℝ) ^ ε := by
      rw [Real.mul_rpow hC3p.le (by positivity), ← Real.rpow_mul hp0.le,
        show 3 * ν * ((8 : ℝ) + 1) = ε by rw [hνdef]; ring]
      ring

/-- **Erdős Problem 985 for large primes.** Under `ZeroFree`, every prime `p ≥ p₀` has a prime
`q < p` that is a primitive root modulo `p`. -/
theorem erdos_985_of_large (hZ : ZeroFree) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  obtain ⟨C, hC, h⟩ := least_prime_primitive_root_le_rpow hZ (ε := 1 / 2) (by norm_num)
  refine ⟨⌈C ^ 2⌉₊ + 1, fun p hp hp₀ => ?_⟩
  obtain ⟨q, hq, hord, hle⟩ := h p hp
  refine ⟨q, hq, ?_, hord⟩
  have hpC : C ^ 2 < p := by
    have h1 := Nat.le_ceil (C ^ 2)
    have h2 : ((⌈C ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hp₀
    linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsq : C < (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.lt_sqrt hC.le).mpr hpC
  have hlt : (q : ℝ) < p := by
    calc (q : ℝ) ≤ C * (p : ℝ) ^ (1 / 2 : ℝ) := hle
      _ < (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
        gcongr
      _ = p := by
        rw [← Real.rpow_add hp0]
        norm_num
  exact_mod_cast hlt

end Vinogradov.Main
