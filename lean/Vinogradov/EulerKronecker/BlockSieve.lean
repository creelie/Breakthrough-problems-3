/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

Brun–Titchmarsh for the progression `1 mod q` on dyadic blocks, from the Selberg sieve of
`PrimeNumberTheoremAnd` (Arend Mellendijk).
-/
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds
import Mathlib

set_option lang.lemmaCmd true

noncomputable section

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve Sieve
open scoped Finset

namespace Vinogradov.EulerKronecker

/-- The term `1 + (M + m) q` of the progression `1 mod q`. -/
def apTerm (q M m : ℕ) : ℕ := 1 + (M + m) * q

lemma apTerm_strictMono {q : ℕ} (hq : 0 < q) (M : ℕ) : StrictMono (apTerm q M) := by
  intro a b hab
  unfold apTerm
  have : (M + a) * q < (M + b) * q := Nat.mul_lt_mul_of_pos_right (by omega) hq
  omega

/-- The terms of the block `m < M` lie in `(M q, 2 M q]`. -/
lemma apTerm_mem {q M m : ℕ} (hq : 0 < q) (hm : m < M) :
    M * q < apTerm q M m ∧ apTerm q M m ≤ 2 * (M * q) := by
  unfold apTerm
  constructor
  · have : M * q ≤ (M + m) * q := Nat.mul_le_mul_right q (by omega)
    omega
  · have h1 : (M + m) * q + q ≤ 2 * (M * q) := by
      have h2 : (M + m + 1) * q ≤ (2 * M) * q := Nat.mul_le_mul_right q (by omega)
      calc (M + m) * q + q = (M + m + 1) * q := by ring
        _ ≤ (2 * M) * q := h2
        _ = 2 * (M * q) := by ring
    omega

/-- The sieve on the block `1 + (M + m) q`, `m < M`, sifting by the primes up to `z`. -/
def apSieve (q M : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range M).image (apTerm q M)
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := M
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

theorem siftedSum_apSieve {q : ℕ} (hq : 0 < q) (M : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    siftedSum (s := (apSieve q M z hz).toBoundingSieve) =
      (#{m ∈ Finset.range M | Nat.Coprime (primorial ⌊z⌋₊) (apTerm q M m)} : ℝ) := by
  simp only [siftedSum, apSieve]
  rw [Finset.sum_image (fun a _ b _ hab => (apTerm_strictMono hq M).injective hab),
    Finset.card_filter]
  push_cast
  rfl

theorem multSum_apSieve {q : ℕ} (hq : 0 < q) (M : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    multSum (s := (apSieve q M z hz).toBoundingSieve) d =
      (#{m ∈ Finset.range M | d ∣ apTerm q M m} : ℝ) := by
  simp only [multSum, apSieve]
  rw [Finset.sum_image (fun a _ b _ hab => (apTerm_strictMono hq M).injective hab),
    Finset.sum_boole]

/-- For `d` coprime to `q`, the condition `d ∣ 1 + (M + m) q` is one residue class of `m`. -/
theorem dvd_apTerm_iff {q d : ℕ} [NeZero d] (hcop : Nat.Coprime q d) (M : ℕ) :
    ∃ k : ℕ, ∀ m : ℕ, d ∣ apTerm q M m ↔ m ≡ k [MOD d] := by
  set U : (ZMod d)ˣ := ZMod.unitOfCoprime q hcop with hU
  have hUq : ((U : ZMod d)) = (q : ZMod d) := rfl
  set c : ZMod d := -((U⁻¹ : (ZMod d)ˣ) : ZMod d) - (M : ZMod d) with hc
  refine ⟨c.val, fun m => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  unfold apTerm
  push_cast
  rw [← hUq]
  constructor
  · intro h
    have h2 : ((U⁻¹ : (ZMod d)ˣ) : ZMod d) * (1 + (M + m) * (U : ZMod d)) = 0 := by
      rw [h, mul_zero]
    have h3 : ((U⁻¹ : (ZMod d)ˣ) : ZMod d) * (U : ZMod d) = 1 := Units.inv_mul U
    rw [hc]
    linear_combination h2 - ((M : ZMod d) + m) * h3
  · intro h
    have h3 : ((U⁻¹ : (ZMod d)ˣ) : ZMod d) * (U : ZMod d) = 1 := Units.inv_mul U
    have h2 : ((U⁻¹ : (ZMod d)ˣ) : ZMod d) * (1 + (M + m) * (U : ZMod d)) = 0 := by
      rw [h, hc]
      linear_combination ((-(((U⁻¹ : (ZMod d)ˣ) : ZMod d)) - M) + M) * h3
    exact (Units.mul_right_eq_zero U⁻¹).mp h2

/-- The number of `m < M` in one residue class modulo `d` differs from `M / d` by at most one. -/
theorem abs_card_modEq_sub_le (M d k : ℕ) (hd : 0 < d) :
    |(#{m ∈ Finset.range M | m ≡ k [MOD d]} : ℝ) - M / (d : ℝ)| ≤ 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card M hd]
  have hm : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : ((M / d : ℕ) : ℝ) ≤ (M:ℝ) / (d : ℝ) := Nat.cast_div_le
  have h2 : (M:ℝ) / (d : ℝ) < ((M / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hm]
    have := Nat.lt_div_mul_add (a := M) hd
    have h3 : (M:ℝ) < ((M / d : ℕ) : ℝ) * (d : ℝ) + (d : ℝ) := by exact_mod_cast this
    rw [add_mul, one_mul]; exact h3
  rw [abs_le]
  split_ifs <;> push_cast at h1 h2 ⊢ <;> constructor <;> linarith

/-- Every divisor of the primorial of `⌊z⌋` with `z < q` is coprime to the prime `q`. -/
theorem coprime_of_dvd_primorial {q d : ℕ} (hq : q.Prime) {z : ℝ} (hzq : z < q)
    (hd : d ∣ primorial ⌊z⌋₊) : Nat.Coprime q d := by
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hqd
  have h := (prime_dvd_primorial_iff _ _ hq).mp (hqd.trans hd)
  have hz0 : 0 ≤ z := by
    by_contra h0
    push Not at h0
    rw [Nat.floor_of_nonpos h0.le] at h
    exact hq.ne_zero (by omega)
  have : (q : ℝ) ≤ z := (Nat.le_floor_iff hz0).mp h
  linarith

theorem abs_rem_apSieve_le {q : ℕ} (hq : q.Prime) (M : ℕ) {z : ℝ} (hz : 1 ≤ z) (hzq : z < q)
    {d : ℕ} (hd : d ∣ primorial ⌊z⌋₊) :
    |rem (s := (apSieve q M z hz).toBoundingSieve) d| ≤ 1 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (Nat.pos_iff_ne_zero.mp (primorial_pos _)) (Nat.eq_zero_of_zero_dvd hd)
  have : NeZero d := ⟨hd0⟩
  obtain ⟨k, hk⟩ := dvd_apTerm_iff (coprime_of_dvd_primorial hq hzq hd) M
  have hfilter : {m ∈ Finset.range M | d ∣ apTerm q M m} =
      {m ∈ Finset.range M | m ≡ k [MOD d]} := Finset.filter_congr (fun m _ => hk m)
  unfold rem
  rw [multSum_apSieve hq.pos, hfilter]
  have hnu : (apSieve q M z hz).nu d = 1 / (d : ℝ) := by
    simp [apSieve, hd0]
  have htm : (apSieve q M z hz).totalMass = M := rfl
  rw [show (apSieve q M z hz).toBoundingSieve.nu d = (apSieve q M z hz).nu d from rfl,
    show (apSieve q M z hz).toBoundingSieve.totalMass = (apSieve q M z hz).totalMass from rfl,
    hnu, htm, one_div, inv_mul_eq_div]
  exact abs_card_modEq_sub_le M d k (Nat.pos_of_ne_zero hd0)

/-- `rem_sum_le_of_const` with the remainder bound required only on divisors of the sifting
product. -/
theorem rem_sum_le_of_const_dvd (s : SelbergSieve) (C : ℝ)
    (hrem : ∀ d, d ∣ s.prodPrimes → |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then
        (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors), 3 ^ ω d * C)
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact hrem d hd.1.1
  rw [← Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (one_dvd _)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  exact s.prodPrimes_squarefree

/-- **Brun–Titchmarsh on a block.** At most `2M / log z + z (1 + log z)^3` of the numbers
`1 + (M + m) q`, `m < M`, are free of prime factors up to `z`, when `1 < z < q`. -/
theorem card_coprime_le {q : ℕ} (hq : q.Prime) (M : ℕ) {z : ℝ} (hz : 1 < z) (hzq : z < q) :
    (#{m ∈ Finset.range M | Nat.Coprime (primorial ⌊z⌋₊) (apTerm q M m)} : ℝ) ≤
      2 * M / Real.log z + z * (1 + Real.log z) ^ 3 := by
  rw [← siftedSum_apSieve hq.pos M z hz.le]
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  have hS : (apSieve q M z hz.le).selbergBoundingSum ≥ Real.log z / 2 := by
    apply boundingSum_ge_log
    · rfl
    · intro p hpp hp
      show p ∣ primorial ⌊z⌋₊
      rw [prime_dvd_primorial_iff _ _ hpp]
      exact Nat.le_floor hp
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hR := rem_sum_le_of_const_dvd (apSieve q M z hz.le) 1
    (fun d hd => abs_rem_apSieve_le hq M hz.le hzq hd)
  have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : (apSieve q M z hz.le).totalMass / (apSieve q M z hz.le).selbergBoundingSum ≤
      (M : ℝ) / (Real.log z / 2) :=
    div_le_div_of_nonneg_left hM (by positivity) hS
  calc _ ≤ (M : ℝ) / (Real.log z / 2) + 1 * z * (1 + Real.log z) ^ 3 := add_le_add h1 hR
    _ = 2 * M / Real.log z + z * (1 + Real.log z) ^ 3 := by field_simp

/-- A prime power that is not coprime to the primorial of `⌊z⌋` has its prime at most `z`. -/
lemma minFac_le_of_not_coprime {n : ℕ} (hn : IsPrimePow n) {z : ℝ}
    (h : ¬ Nat.Coprime (primorial ⌊z⌋₊) n) : n.minFac ≤ ⌊z⌋₊ := by
  have hmf := hn.minFac_pow_factorization_eq
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  by_contra hlt
  apply h
  rw [← hmf]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp, prime_dvd_primorial_iff _ _ hp]
  exact hlt

/-- In a block, at most one term is a power of a given prime. -/
lemma minFac_injOn {q M : ℕ} (hq : 0 < q) :
    Set.InjOn (fun m => (apTerm q M m).minFac)
      {m | m < M ∧ IsPrimePow (apTerm q M m)} := by
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq] at ha hb hab
  obtain ⟨haM, hap⟩ := ha
  obtain ⟨hbM, hbp⟩ := hb
  set p := (apTerm q M a).minFac with hpdef
  have hp2 : 2 ≤ p := (Nat.minFac_prime hap.ne_one).two_le
  have ea := hap.minFac_pow_factorization_eq
  have eb := hbp.minFac_pow_factorization_eq
  rw [← hpdef] at ea
  rw [← hab] at eb
  set ka := (apTerm q M a).factorization p
  set kb := (apTerm q M b).factorization ((apTerm q M b).minFac) with hkb
  rw [← hab] at hkb
  obtain ⟨ha1, ha2⟩ := apTerm_mem hq haM
  obtain ⟨hb1, hb2⟩ := apTerm_mem hq hbM
  have key : ∀ i j : ℕ, i < j → p ^ j ≥ 2 * p ^ i := by
    intro i j hij
    calc p ^ j ≥ p ^ (i + 1) := Nat.pow_le_pow_right (by omega) hij
      _ = p ^ i * p := pow_succ p i
      _ ≥ p ^ i * 2 := Nat.mul_le_mul_left _ hp2
      _ = 2 * p ^ i := by ring
  have eb' : apTerm q M b = p ^ (apTerm q M b).factorization p := by
    rw [hab] at eb ⊢; exact eb.symm
  have ea' : apTerm q M a = p ^ ka := ea.symm
  have hval : apTerm q M a = apTerm q M b := by
    rcases lt_trichotomy ka ((apTerm q M b).factorization p) with h | h | h
    · have := key _ _ h
      rw [← ea', ← eb'] at this
      omega
    · rw [ea', eb', h]
    · have := key _ _ h
      rw [← ea', ← eb'] at this
      omega
  exact (apTerm_strictMono hq M).injective hval

/-- **Prime powers on a block.** At most `2M / log z + z (1 + log z)^3 + z` of the numbers
`1 + (M + m) q`, `m < M`, are prime powers, when `1 < z < q` and `q` is prime. -/
theorem card_primePow_le {q : ℕ} (hq : q.Prime) (M : ℕ) {z : ℝ} (hz : 1 < z) (hzq : z < q) :
    (#{m ∈ Finset.range M | IsPrimePow (apTerm q M m)} : ℝ) ≤
      2 * M / Real.log z + z * (1 + Real.log z) ^ 3 + z := by
  set A := {m ∈ Finset.range M | Nat.Coprime (primorial ⌊z⌋₊) (apTerm q M m)}
  set B := {m ∈ Finset.range M | IsPrimePow (apTerm q M m) ∧ (apTerm q M m).minFac ≤ ⌊z⌋₊}
  have hsub : {m ∈ Finset.range M | IsPrimePow (apTerm q M m)} ⊆ A ∪ B := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hc : Nat.Coprime (primorial ⌊z⌋₊) (apTerm q M m)
    · exact Or.inl ⟨hm.1, hc⟩
    · exact Or.inr ⟨hm.1, hm.2, minFac_le_of_not_coprime hm.2 hc⟩
  have hB : (#B : ℝ) ≤ z := by
    have hinj : Set.InjOn (fun m => (apTerm q M m).minFac) (B : Set ℕ) := by
      apply (minFac_injOn hq.pos).mono
      intro m hm
      simp only [B, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm
      exact ⟨hm.1, hm.2.1⟩
    have hcard : #B = #(B.image (fun m => (apTerm q M m).minFac)) :=
      (Finset.card_image_of_injOn hinj).symm
    have himg : B.image (fun m => (apTerm q M m).minFac) ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨m, hm, rfl⟩ := hp
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Icc]
      exact ⟨Nat.minFac_pos _, hm.2.2⟩
    have h1 : #B ≤ ⌊z⌋₊ := by
      rw [hcard]
      calc _ ≤ #(Finset.Icc 1 ⌊z⌋₊) := Finset.card_le_card himg
        _ = ⌊z⌋₊ := by simp
    calc (#B : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ z := Nat.floor_le (by linarith)
  calc (#{m ∈ Finset.range M | IsPrimePow (apTerm q M m)} : ℝ) ≤ (#(A ∪ B) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (#A : ℝ) + #B := by exact_mod_cast Finset.card_union_le A B
    _ ≤ _ := by gcongr; exact card_coprime_le hq M hz hzq

end Vinogradov.EulerKronecker
