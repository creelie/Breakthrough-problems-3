/-
Copyright (c) 2026 Deep Bhattacharjee. Released under Apache 2.0 license.

An upper bound for prime pairs `(n, n + h)` from the Selberg sieve of
`PrimeNumberTheoremAnd` (Arend Mellendijk).
-/
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Order.Field.GeomSum

set_option lang.lemmaCmd true

noncomputable section

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve Sieve
open scoped Finset

namespace Vinogradov.MV

/-- The bounding-sum lower bound of `Sieve.selbergBoundingSum_ge_sum_div`, for any set of
integers `m ≤ √y` whose prime factors divide the sifting product. -/
theorem boundingSum_ge_sum_of_dvd (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1)
    (A : Finset ℕ) (hA : ∀ m ∈ A, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt s.level)
    (hAP : ∀ m ∈ A, ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes) :
    ∑ m ∈ A, s.nu m ≤ s.selbergBoundingSum := by
  unfold selbergBoundingSum
  calc ∑ m ∈ A, s.nu m
     ≤ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m := ?_
   _ ≤ ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then SelbergSieve.selbergTerms s.toBoundingSieve l else 0) := ?_
  swap
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg
  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hmA
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    have hm := hA m hmA
    have hm_ne_zero : m ≠ 0 := by
      exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
    use ∏ p ∈ m.primeFactors, p
    constructor; constructor; constructor
    · apply prod_primes_dvd_of_dvd <;> intro p hp
      · exact hAP m hmA p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.prime_of_mem_primeFactors hp
    · exact prodPrimes_ne_zero
    · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
      · trans (m:ℝ)
        · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
          exact Nat.prod_primeFactors_dvd m
        exact hm.2
      apply le_of_lt; norm_cast
    constructor; constructor
    · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
      · intro p
        have hy_mul_prod_nonneg :
            0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
          apply mul_nonneg
          · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
          · norm_num
        trans (Nat.factorization m) p * 1
        · rw [mul_one]
        rw [Finsupp.smul_apply, smul_eq_mul]
        by_cases hpp : p.Prime
        swap
        · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
        by_cases hpdvd : p ∣ m
        swap
        · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
        apply mul_le_mul
        · trans m
          · apply le_of_lt <| Nat.factorization_lt _ _
            apply hm_ne_zero
          apply Nat.le_floor
          refine le_trans hm.2 ?_
          apply sqrt_le_self _ s.one_le_level
        · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
          apply Finset.dvd_prod_of_mem
          rw [Nat.mem_primeFactors]
          exact ⟨hpp, hpdvd, hm_ne_zero⟩
        · norm_num
        · norm_num
      exact hm_ne_zero
    · exact hprod_ne_zero
    · exact Nat.prod_primeFactors_dvd m
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

/-- The density `2^Ω(n)/n`, completely multiplicative. -/
def nuP : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (2 : ℝ) ^ (ArithmeticFunction.cardFactors n) / n, by simp⟩

theorem nuP_apply {n : ℕ} (hn : n ≠ 0) :
    nuP n = (2 : ℝ) ^ (ArithmeticFunction.cardFactors n) / n := by
  simp [nuP, hn]

theorem nuP_cm : CompletelyMultiplicative nuP := by
  constructor
  · rw [nuP_apply one_ne_zero]; simp
  intro a b
  rcases eq_or_ne a 0 with rfl | ha
  · simp [nuP]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [nuP]
  rw [nuP_apply ha, nuP_apply hb, nuP_apply (mul_ne_zero ha hb),
    ArithmeticFunction.cardFactors_mul ha hb, pow_add, Nat.cast_mul]
  field_simp

theorem nuP_nonneg (n : ℕ) : 0 ≤ nuP n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [nuP_apply hn]; positivity

theorem nuP_prime {p : ℕ} (hp : p.Prime) : nuP p = 2 / p := by
  rw [nuP_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

/-- The primes up to `z` that do not divide `h`. -/
def sieveSet (z h : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ h)

def sieveP (z h : ℕ) : ℕ := ∏ p ∈ sieveSet z h, p

theorem prime_of_mem_sieveSet {z h p : ℕ} (hp : p ∈ sieveSet z h) : p.Prime :=
  (Finset.mem_filter.mp hp).2.1

theorem sieveP_squarefree (z h : ℕ) : Squarefree (sieveP z h) :=
  prodDistinctPrimes_squarefree _ (fun _ hp => prime_of_mem_sieveSet hp)

theorem mem_sieveSet_of_dvd {z h q : ℕ} (hq : q.Prime) (hqP : q ∣ sieveP z h) :
    q ∈ sieveSet z h := by
  obtain ⟨p, hp, hqp⟩ := hq.prime.exists_mem_finset_dvd hqP
  rwa [(Nat.prime_dvd_prime_iff_eq hq (prime_of_mem_sieveSet hp)).mp hqp]

theorem dvd_sieveP {z h p : ℕ} (hp : p ∈ sieveSet z h) : p ∣ sieveP z h :=
  Finset.dvd_prod_of_mem _ hp

theorem three_le_of_mem_sieveSet {z h p : ℕ} (hh : 2 ∣ h) (hp : p ∈ sieveSet z h) : 3 ≤ p := by
  have h2 := (Finset.mem_filter.mp hp).2
  rcases h2.1.eq_two_or_odd' with h2' | hodd
  · exact absurd (h2' ▸ hh) h2.2
  · have := h2.1.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · interval_cases p; exact absurd hodd (by decide)
    · exact hge

/-- The Selberg sieve for the products `n (n + h)`, `n < X`, sifted by the primes up to `z`
not dividing `h`, at level `y`. -/
def pairSieve (X h z : ℕ) (hh : 2 ∣ h) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := (Finset.range X).image (fun n => n * (n + h))
  prodPrimes := sieveP z h
  prodPrimes_squarefree := sieveP_squarefree z h
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := X
  nu := nuP
  nu_mult := nuP_cm.isMultiplicative
  nu_pos_of_prime := fun p hp _ => by rw [nuP_prime hp]; have := hp.pos; positivity
  nu_lt_one_of_prime := fun p hp hpP => by
    rw [nuP_prime hp]
    have h3 := three_le_of_mem_sieveSet hh (mem_sieveSet_of_dvd hp hpP)
    rw [div_lt_one (by positivity)]
    exact_mod_cast (by omega : 2 < p)
  level := y
  one_le_level := hy

theorem mul_add_injective (h : ℕ) : Function.Injective (fun n : ℕ => n * (n + h)) := by
  apply StrictMono.injective
  intro a b hab
  exact Nat.mul_lt_mul'' hab (Nat.add_lt_add_right hab h)

theorem siftedSum_pairSieve (X h z : ℕ) (hh : 2 ∣ h) (y : ℝ) (hy : 1 ≤ y) :
    siftedSum (s := (pairSieve X h z hh y hy).toBoundingSieve) =
      (#{n ∈ Finset.range X | Nat.Coprime (sieveP z h) (n * (n + h))} : ℝ) := by
  simp only [siftedSum, pairSieve]
  rw [Finset.sum_image (fun a _ b _ hab => mul_add_injective h hab), Finset.card_filter]
  push_cast
  rfl

theorem multSum_pairSieve (X h z : ℕ) (hh : 2 ∣ h) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) :
    multSum (s := (pairSieve X h z hh y hy).toBoundingSieve) d =
      (#{n ∈ Finset.range X | d ∣ n * (n + h)} : ℝ) := by
  simp only [multSum, pairSieve]
  rw [Finset.sum_image (fun a _ b _ hab => mul_add_injective h hab), Finset.sum_boole]

/-- Prime pairs below `X` lie below `z + 1` or survive the sieve. -/
theorem pairs_le_sifted (X h z : ℕ) :
    #{n ∈ Finset.range X | n.Prime ∧ (n + h).Prime} ≤
      (z + 1) + #{n ∈ Finset.range X | Nat.Coprime (sieveP z h) (n * (n + h))} := by
  calc _ ≤ #(Finset.range (z + 1) ∪
        {n ∈ Finset.range X | Nat.Coprime (sieveP z h) (n * (n + h))}) := by
        apply Finset.card_le_card
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
        by_cases hnz : n < z + 1
        · left; exact hnz
        right
        refine ⟨hn.1, Nat.coprime_of_dvd fun k hk hkP hkn => ?_⟩
        have hks := Finset.mem_filter.mp (mem_sieveSet_of_dvd hk hkP)
        have hkz : k < z + 1 := Finset.mem_range.mp hks.1
        rcases (Nat.Prime.dvd_mul hk).mp hkn with h1 | h1
        · have := (Nat.prime_dvd_prime_iff_eq hk hn.2.1).mp h1; omega
        · have := (Nat.prime_dvd_prime_iff_eq hk hn.2.2).mp h1; omega
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans ?_
        rw [Finset.card_range]

/-- For `d` coprime to `h`, the factorisations `d = d₁ d₂` with `d₁ ∣ n`, `d₂ ∣ n + h` number
one if `d ∣ n (n + h)` and none otherwise. -/
theorem card_pairs_dvd (d h n : ℕ) (hd : d ≠ 0) (hdh : Nat.Coprime d h) :
    #{x ∈ d.divisorsAntidiagonal | x.1 ∣ n ∧ x.2 ∣ n + h} =
      if d ∣ n * (n + h) then 1 else 0 := by
  split_ifs with hdiv
  · rw [Finset.card_eq_one]
    refine ⟨(Nat.gcd d n, d / Nat.gcd d n), ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    have hg : Nat.gcd d n ∣ d := Nat.gcd_dvd_left d n
    have hgpos : 0 < Nat.gcd d n := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd)
    constructor
    · rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
      refine ⟨⟨Nat.mul_div_cancel' hg, hd⟩, Nat.gcd_dvd_right d n, ?_⟩
      have h1 : d / Nat.gcd d n ∣ n / Nat.gcd d n * (n + h) := by
        have := Nat.div_dvd_div hg hdiv
        rwa [Nat.mul_div_right_comm (Nat.gcd_dvd_right d n)] at this
      exact (Nat.coprime_div_gcd_div_gcd hgpos).dvd_of_dvd_mul_left h1
    · rintro ⟨d1, d2⟩ hx
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
      obtain ⟨⟨hprod, -⟩, h1, h2⟩ := hx
      have hd1 : d1 ∣ Nat.gcd d n := Nat.dvd_gcd (hprod ▸ dvd_mul_right d1 d2) h1
      have hcop : Nat.Coprime (Nat.gcd d n) d2 := by
        apply Nat.coprime_of_dvd
        intro k hk hkg hkd2
        have hkn : k ∣ n := hkg.trans (Nat.gcd_dvd_right d n)
        have hkh : k ∣ h := (Nat.dvd_add_right hkn).mp (hkd2.trans h2)
        have hkd : k ∣ d := hkg.trans hg
        exact hk.ne_one ((Nat.Coprime.coprime_dvd_left hkd hdh).eq_one_of_dvd hkh)
      have hgd1 : Nat.gcd d n ∣ d1 := hcop.dvd_of_dvd_mul_right (hprod ▸ hg)
      have he : d1 = Nat.gcd d n := Nat.dvd_antisymm hd1 hgd1
      refine Prod.ext he ?_
      show d2 = d / Nat.gcd d n
      rw [← he]
      exact (Nat.div_eq_of_eq_mul_left (he ▸ hgpos) (by rw [← hprod, mul_comm])).symm
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨d1, d2⟩ hx ⟨h1, h2⟩
    rw [Nat.mem_divisorsAntidiagonal] at hx
    exact hdiv (hx.1 ▸ mul_dvd_mul h1 h2)

theorem card_dvd_mul_add_eq (X h d : ℕ) (hd : d ≠ 0) (hdh : Nat.Coprime d h) :
    #{n ∈ Finset.range X | d ∣ n * (n + h)} =
      ∑ x ∈ d.divisorsAntidiagonal, #{n ∈ Finset.range X | x.1 ∣ n ∧ x.2 ∣ n + h} := by
  calc #{n ∈ Finset.range X | d ∣ n * (n + h)}
      = ∑ n ∈ Finset.range X, #{x ∈ d.divisorsAntidiagonal | x.1 ∣ n ∧ x.2 ∣ n + h} := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun n _ => (card_pairs_dvd d h n hd hdh).symm)
    _ = _ := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm

/-- The integers below `X` with `d₁ ∣ n` and `d₂ ∣ n + h` form one residue class modulo `d₁ d₂`. -/
theorem abs_card_dvd_dvd_sub_le (X h d1 d2 : ℕ) (hco : Nat.Coprime d1 d2) (hpos : 0 < d1 * d2) :
    |(#{n ∈ Finset.range X | d1 ∣ n ∧ d2 ∣ n + h} : ℝ) - X / ((d1 * d2 : ℕ) : ℝ)| ≤ 1 := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco 0 ((d2 - 1) * h)
  have hd2 : 0 < d2 := Nat.pos_of_mul_pos_left hpos
  have e : (d2 - 1) * h + h = d2 * h := by
    obtain ⟨c, rfl⟩ : ∃ c, d2 = c + 1 := ⟨d2 - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have hfilter : {n ∈ Finset.range X | d1 ∣ n ∧ d2 ∣ n + h} =
      {n ∈ Finset.range X | n ≡ k [MOD d1 * d2]} := by
    apply Finset.filter_congr
    intro n _
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hco]
    have key : d2 ∣ n + h ↔ n ≡ (d2 - 1) * h [MOD d2] := by
      constructor
      · intro h2
        apply Nat.ModEq.add_right_cancel' h
        rw [e]
        exact (Nat.modEq_zero_iff_dvd.mpr h2).trans
          (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d2 h)).symm
      · intro h2
        have := Nat.ModEq.add_right h h2
        rw [e] at this
        exact Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d2 h)))
    rw [key, ← Nat.modEq_zero_iff_dvd]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans hk1.symm, h2.trans hk2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.trans hk1, h2.trans hk2⟩
  rw [hfilter, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card X hpos]
  have hm : (0:ℝ) < ((d1 * d2 : ℕ) : ℝ) := by exact_mod_cast hpos
  have h1 : ((X / (d1 * d2) : ℕ) : ℝ) ≤ (X:ℝ) / ((d1 * d2 : ℕ) : ℝ) := Nat.cast_div_le
  have h2 : (X:ℝ) / ((d1 * d2 : ℕ) : ℝ) < ((X / (d1 * d2) : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hm]
    have := Nat.lt_div_mul_add (a := X) hpos
    have h3 : (X:ℝ) < ((X / (d1 * d2) : ℕ) : ℝ) * ((d1 * d2 : ℕ) : ℝ) + ((d1 * d2 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [add_mul, one_mul]; exact h3
  rw [abs_le]
  split_ifs <;> push_cast at h1 h2 ⊢ <;> constructor <;> linarith

theorem card_divisors_of_squarefree {d : ℕ} (hd : Squarefree d) :
    #d.divisors = 2 ^ ArithmeticFunction.cardFactors d := by
  have hd0 := hd.ne_zero
  have hone : ∀ p ∈ d.primeFactors, d.factorization p = 1 := by
    intro p hp
    have h1 := hd.natFactorization_le_one p
    have h2 : d.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
    omega
  have hprod : ∏ p ∈ d.primeFactors, (d.factorization p + 1) = ∏ p ∈ d.primeFactors, 2 :=
    Finset.prod_congr rfl (fun p hp => by rw [hone p hp])
  rw [Nat.card_divisors hd0, ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, hprod, Finset.sum_congr rfl hone, Finset.prod_const,
    Finset.sum_const, smul_eq_mul, mul_one]

theorem card_divisors_le_two_pow {m : ℕ} (hm : m ≠ 0) :
    #m.divisors ≤ 2 ^ ArithmeticFunction.cardFactors m := by
  rw [Nat.card_divisors hm, ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun p _ => Nat.succ_le_of_lt Nat.lt_two_pow_self

theorem coprime_of_dvd_sieveP {z h d : ℕ} (hd : d ∣ sieveP z h) : Nat.Coprime d h := by
  apply Nat.coprime_of_dvd
  intro k hk hkd hkh
  exact (Finset.mem_filter.mp (mem_sieveSet_of_dvd hk (hkd.trans hd))).2.2 hkh

/-- The remainder of the pair sieve: `|R_d| ≤ τ(d)`. -/
theorem abs_rem_pairSieve_le (X h z : ℕ) (hh : 2 ∣ h) (y : ℝ) (hy : 1 ≤ y) {d : ℕ}
    (hd : d ∣ sieveP z h) :
    |rem (s := (pairSieve X h z hh y hy).toBoundingSieve) d| ≤ #d.divisors := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (sieveP_squarefree z h)
  have hd0 := hsq.ne_zero
  have hdh : Nat.Coprime d h := coprime_of_dvd_sieveP hd
  have hcard : #d.divisorsAntidiagonal = #d.divisors := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  rw [BoundingSieve.rem, multSum_pairSieve]
  change |(_:ℝ) - nuP d * (X:ℝ)| ≤ _
  have h2 : (2:ℝ) ^ ArithmeticFunction.cardFactors d = (#d.divisorsAntidiagonal : ℝ) := by
    rw [hcard, card_divisors_of_squarefree hsq]; push_cast; ring
  rw [nuP_apply hd0, h2, card_dvd_mul_add_eq X h d hd0 hdh]
  push_cast
  have : (#d.divisorsAntidiagonal : ℝ) / d * X = ∑ x ∈ d.divisorsAntidiagonal, (X:ℝ) / d := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [this, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ x ∈ d.divisorsAntidiagonal, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Nat.mem_divisorsAntidiagonal] at hx
        have hsq' : Squarefree (x.1 * x.2) := by rw [hx.1]; exact hsq
        have hco : Nat.Coprime x.1 x.2 := Nat.coprime_of_squarefree_mul hsq'
        have := abs_card_dvd_dvd_sub_le X h x.1 x.2 hco (by rw [hx.1]; exact Nat.pos_of_ne_zero hd0)
        rwa [hx.1] at this
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

theorem three_pow_omega_le {z h d : ℕ} (hh : 2 ∣ h) (hd : d ∣ sieveP z h) : 3 ^ ω d ≤ d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (sieveP_squarefree z h)
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.pow_card_le_prod
  intro p hp
  exact three_le_of_mem_sieveSet hh (mem_sieveSet_of_dvd (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans hd))

/-- The error term of the pair sieve is at most `y³`. -/
theorem errSum_pairSieve_le (X h z : ℕ) (hh : 2 ∣ h) (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Nat.divisors (sieveP z h), (if (d:ℝ) ≤ y then
      (3:ℝ) ^ ω d * |rem (s := (pairSieve X h z hh y hy).toBoundingSieve) d| else 0) ≤ y ^ 3 := by
  calc _ ≤ ∑ d ∈ (Nat.divisors (sieveP z h)).filter (fun d : ℕ => (d:ℝ) ≤ y), y ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro d hd
        split_ifs with hdy
        · have hdP := Nat.dvd_of_mem_divisors hd
          have h3 : (3:ℝ) ^ ω d ≤ d := by exact_mod_cast three_pow_omega_le hh hdP
          have hR : |rem (s := (pairSieve X h z hh y hy).toBoundingSieve) d| ≤ d :=
            (abs_rem_pairSieve_le X h z hh y hy hdP).trans
              (by exact_mod_cast Nat.card_divisors_le_self d)
          calc (3:ℝ) ^ ω d * |rem (s := (pairSieve X h z hh y hy).toBoundingSieve) d|
              ≤ d * d := mul_le_mul h3 hR (abs_nonneg _) (Nat.cast_nonneg _)
            _ ≤ y * y := mul_le_mul hdy hdy (Nat.cast_nonneg _) (by linarith)
            _ = y ^ 2 := by ring
        · exact le_rfl
    _ ≤ y ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hsub : (Nat.divisors (sieveP z h)).filter (fun d : ℕ => (d:ℝ) ≤ y) ⊆
            Finset.Icc 1 ⌊y⌋₊ := by
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [Finset.mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
        have hc : (#((Nat.divisors (sieveP z h)).filter (fun d : ℕ => (d:ℝ) ≤ y)) : ℝ) ≤ y := by
          calc _ ≤ (#(Finset.Icc 1 ⌊y⌋₊) : ℝ) := by exact_mod_cast Finset.card_le_card hsub
            _ = ⌊y⌋₊ := by simp
            _ ≤ y := Nat.floor_le (by linarith)
        calc _ ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
          _ = y ^ 3 := by ring

/-- The reciprocal sum over `a ≤ T` with no prime factor in `s`. -/
def Hs (s : Finset ℕ) (T : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 T).filter (fun a => ∀ p ∈ s, ¬ p ∣ a), (a:ℝ)⁻¹

theorem geom_inv_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((p:ℝ) ^ k)⁻¹ ≤ p / (p - 1 : ℝ) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) (by positivity) hlt
  rw [← Finset.range_eq_Ico] at h
  simp_rw [← inv_pow]
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  calc _ ≤ _ := h
    _ = _ := by field_simp

/-- Removing the prime `p` from a reciprocal sum costs at most the factor `p/(p-1)`. -/
theorem Hs_insert_le (s : Finset ℕ) (T p : ℕ) (hp : p.Prime) :
    Hs s T ≤ (p / (p - 1 : ℝ)) * Hs (insert p s) T := by
  set S1 := (Finset.Icc 1 T).filter (fun a => ∀ q ∈ s, ¬ q ∣ a)
  set S2 := (Finset.Icc 1 T).filter (fun a => ∀ q ∈ insert p s, ¬ q ∣ a)
  let ψ : ℕ → ℕ × ℕ := fun a => (a.factorization p, a / p ^ a.factorization p)
  have hmaps : ∀ a ∈ S1, ψ a ∈ Finset.range (T + 1) ×ˢ S2 := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    have ha0 : a ≠ 0 := by omega
    simp only [ψ, Finset.mem_product, Finset.mem_range, S2, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert, forall_eq_or_imp]
    refine ⟨?_, ⟨Nat.ordCompl_pos p ha0,
      (Nat.le_of_dvd (by omega) (Nat.ordCompl_dvd a p)).trans ha.1.2⟩,
      Nat.not_dvd_ordCompl hp ha0, fun q hq hqd => ha.2 q hq (hqd.trans (Nat.ordCompl_dvd a p))⟩
    have h1 : a.factorization p < p ^ a.factorization p := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ a.factorization p ≤ a := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd a p)
    omega
  have hinj : Set.InjOn ψ S1 := by
    intro a _ b _ hab
    simp only [ψ, Prod.mk.injEq] at hab
    have ha := Nat.ordProj_mul_ordCompl_eq_self a p
    have hb := Nat.ordProj_mul_ordCompl_eq_self b p
    rw [hab.2, hab.1] at ha
    exact ha.symm.trans hb
  have hF : ∀ a ∈ S1, (a:ℝ)⁻¹ =
      (fun x : ℕ × ℕ => ((p:ℝ) ^ x.1)⁻¹ * ((x.2 : ℕ) : ℝ)⁻¹) (ψ a) := by
    intro a _
    simp only [ψ]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self a p]
    rw [Nat.cast_mul, Nat.cast_pow, mul_inv]
  unfold Hs
  calc ∑ a ∈ S1, (a:ℝ)⁻¹
      = ∑ a ∈ S1, (fun x : ℕ × ℕ => ((p:ℝ) ^ x.1)⁻¹ * ((x.2 : ℕ) : ℝ)⁻¹) (ψ a) :=
        Finset.sum_congr rfl hF
    _ = ∑ x ∈ S1.image ψ, ((p:ℝ) ^ x.1)⁻¹ * ((x.2 : ℕ) : ℝ)⁻¹ := (Finset.sum_image (f := fun x : ℕ × ℕ => ((p:ℝ) ^ x.1)⁻¹ * ((x.2 : ℕ) : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ x ∈ Finset.range (T + 1) ×ˢ S2, ((p:ℝ) ^ x.1)⁻¹ * ((x.2 : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          exact hmaps a ha
        · intro x _ _; positivity
    _ = (∑ k ∈ Finset.range (T + 1), ((p:ℝ) ^ k)⁻¹) * ∑ b ∈ S2, (b:ℝ)⁻¹ := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (geom_inv_le hp _)
        (Finset.sum_nonneg (fun _ _ => by positivity))

theorem Hs_empty_le (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (T : ℕ) :
    Hs ∅ T ≤ (∏ p ∈ t, (p / (p - 1 : ℝ))) * Hs t T := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert p t hpt ih =>
    rw [Finset.prod_insert hpt]
    have ih' := ih (fun q hq => ht q (Finset.mem_insert_of_mem hq))
    have hp := ht p (Finset.mem_insert_self p t)
    have hnn : 0 ≤ ∏ q ∈ t, (q / (q - 1 : ℝ)) := Finset.prod_nonneg (fun q hq => by
      have h1 : (1:ℝ) < q := by exact_mod_cast (ht q (Finset.mem_insert_of_mem hq)).one_lt
      apply div_nonneg <;> linarith)
    calc Hs ∅ T ≤ (∏ q ∈ t, (q / (q - 1 : ℝ))) * Hs t T := ih'
      _ ≤ (∏ q ∈ t, (q / (q - 1 : ℝ))) * ((p / (p - 1 : ℝ)) * Hs (insert p t) T) :=
          mul_le_mul_of_nonneg_left (Hs_insert_le t T p hp) hnn
      _ = _ := by ring

theorem log_le_Hs_empty (T : ℕ) : Real.log (T + 1) ≤ Hs ∅ T := by
  have := Aux.log_add_one_le_sum_inv T
  push_cast at this
  unfold Hs
  simpa using this

/-- `G(h) = ∏_{p ∣ h} p/(p-1)`. -/
def G (h : ℕ) : ℝ := ∏ p ∈ h.primeFactors, (p / (p - 1 : ℝ))

theorem one_le_G (h : ℕ) : 1 ≤ G h := by
  unfold G
  apply Finset.one_le_prod₀
  intro p hp
  have h1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  rw [le_div_iff₀ (by linarith)]; linarith

theorem log_div_G_le_Hs (h T : ℕ) : Real.log (T + 1) / G h ≤ Hs h.primeFactors T := by
  have hG := one_le_G h
  rw [div_le_iff₀ (by linarith), mul_comm]
  exact (log_le_Hs_empty T).trans
    (Hs_empty_le h.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) T)

/-- The Selberg bounding sum of the pair sieve is at least `H_h(T)²`, `T² ≤ √y`. -/
theorem Hs_sq_le_boundingSum (X h z : ℕ) (hh : 2 ∣ h) (hh0 : h ≠ 0) (y : ℝ) (hy : 1 ≤ y)
    (hzy : ⌊y⌋₊ ≤ z) (T : ℕ) (hT : T ^ 2 ≤ ⌊Real.sqrt y⌋₊) :
    Hs h.primeFactors T ^ 2 ≤ (pairSieve X h z hh y hy).selbergBoundingSum := by
  set B := (Finset.Icc 1 T).filter (fun a => ∀ p ∈ h.primeFactors, ¬ p ∣ a)
  set A := (Finset.Icc 1 ⌊Real.sqrt y⌋₊).filter (fun m => ∀ p ∈ h.primeFactors, ¬ p ∣ m)
  have hAB : ∀ x ∈ B ×ˢ B, x.1 * x.2 ∈ A := by
    intro x hx
    simp only [B, A, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by
        have := hx.1.1.1; have := hx.2.1.1; positivity), ?_⟩, ?_⟩
    · calc x.1 * x.2 ≤ T * T := Nat.mul_le_mul hx.1.1.2 hx.2.1.2
        _ = T ^ 2 := by ring
        _ ≤ _ := hT
    · intro p hp hpd
      rcases (Nat.Prime.dvd_mul (Nat.prime_of_mem_primeFactors hp)).mp hpd with h1 | h1
      · exact hx.1.2 p hp h1
      · exact hx.2.2 p hp h1
  have hA : ∀ m ∈ A, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt (pairSieve X h z hh y hy).level := by
    intro m hm
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨hm.1.1, ?_⟩
    calc (m:ℝ) ≤ ⌊Real.sqrt y⌋₊ := by exact_mod_cast hm.1.2
      _ ≤ Real.sqrt y := Nat.floor_le (Real.sqrt_nonneg _)
  have hAP : ∀ m ∈ A, ∀ p, p.Prime → p ∣ m → p ∣ (pairSieve X h z hh y hy).prodPrimes := by
    intro m hm q hq hqm
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hm
    apply dvd_sieveP
    rw [sieveSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hq, fun hqh => hm.2 q (Nat.mem_primeFactors.mpr ⟨hq, hqh, hh0⟩) hqm⟩
    have h1 : q ≤ m := Nat.le_of_dvd (by omega) hqm
    have h2 : ⌊Real.sqrt y⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor (sqrt_le_self y hy)
    omega
  have hfib : ∀ m ∈ A, ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 * x.2 = m),
      ((x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹) ≤ nuP m := by
    intro m hm
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hm
    have hm0 : m ≠ 0 := by omega
    calc ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 * x.2 = m), ((x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹)
        = ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 * x.2 = m), (m : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [← mul_inv, ← hx.2]; push_cast; ring
      _ = #((B ×ˢ B).filter (fun x => x.1 * x.2 = m)) * (m : ℝ)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ #m.divisorsAntidiagonal * (m : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx
            rw [Nat.mem_divisorsAntidiagonal]
            exact ⟨hx.2, hm0⟩)
      _ ≤ (2:ℝ) ^ ArithmeticFunction.cardFactors m * (m : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [← Nat.map_div_right_divisors, Finset.card_map]
          exact_mod_cast card_divisors_le_two_pow hm0
      _ = nuP m := by rw [nuP_apply hm0, div_eq_mul_inv]
  calc Hs h.primeFactors T ^ 2
      = ∑ x ∈ B ×ˢ B, ((x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹) := by
        unfold Hs; rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    _ = ∑ m ∈ A, ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 * x.2 = m),
          ((x.1 : ℝ)⁻¹ * (x.2 : ℝ)⁻¹) := (Finset.sum_fiberwise_of_maps_to hAB _).symm
    _ ≤ ∑ m ∈ A, nuP m := Finset.sum_le_sum hfib
    _ ≤ _ := boundingSum_ge_sum_of_dvd (pairSieve X h z hh y hy) nuP_cm nuP_nonneg
        (pairSieve X h z hh y hy).nu_lt_one_of_prime A hA hAP

/-- Prime pairs: `#{n < X : n and n + h prime} ≤ 400 G(h)² X / log² X + 3 X^{3/5}` for even
`h ≠ 0`. -/
theorem pairs_le (X h : ℕ) (hX : 2 ≤ X) (hh : 2 ∣ h) (hh0 : h ≠ 0) :
    (#{n ∈ Finset.range X | n.Prime ∧ (n + h).Prime} : ℝ) ≤
      400 * G h ^ 2 * X / Real.log X ^ 2 + 3 * (X:ℝ) ^ (3/5 : ℝ) := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  set y : ℝ := (X:ℝ) ^ (1/5 : ℝ) with hydef
  have hy : 1 ≤ y := Real.one_le_rpow hX1 (by norm_num)
  set z := ⌊y⌋₊
  set T := Nat.sqrt ⌊Real.sqrt y⌋₊
  have hT : T ^ 2 ≤ ⌊Real.sqrt y⌋₊ := Nat.sqrt_le' _
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hsel : siftedSum (s := (pairSieve X h z hh y hy).toBoundingSieve) ≤
      (X:ℝ) / (pairSieve X h z hh y hy).selbergBoundingSum + y ^ 3 :=
    ((pairSieve X h z hh y hy).selberg_bound_simple).trans
      (add_le_add le_rfl (errSum_pairSieve_le X h z hh y hy))
  rw [siftedSum_pairSieve] at hsel
  have hS := Hs_sq_le_boundingSum X h z hh hh0 y hy le_rfl T hT
  have hlogT : Real.log X / 20 ≤ Real.log ((T:ℝ) + 1) := by
    have h1 : (⌊Real.sqrt y⌋₊ : ℝ) + 1 ≤ ((T:ℝ) + 1) ^ 2 := by
      have h2 : ⌊Real.sqrt y⌋₊ + 1 ≤ (T + 1) * (T + 1) := Nat.lt_succ_sqrt ⌊Real.sqrt y⌋₊
      have h3 : ((⌊Real.sqrt y⌋₊ + 1 : ℕ) : ℝ) ≤ (((T + 1) * (T + 1) : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3; nlinarith
    have h2 : Real.sqrt y < ((T:ℝ) + 1) ^ 2 := (Nat.lt_floor_add_one _).trans_le h1
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
    have h3 := Real.log_lt_log hsy h2
    rw [Real.log_pow] at h3
    push_cast at h3
    have h4 : Real.log (Real.sqrt y) = Real.log X / 10 := by
      rw [Real.log_sqrt (by linarith), hydef, Real.log_rpow (by linarith)]; ring
    linarith
  have hG := one_le_G h
  have hGpos : 0 < G h := by linarith
  have hHs : Real.log X / (20 * G h) ≤ Hs h.primeFactors T := by
    calc Real.log X / (20 * G h) = (Real.log X / 20) / G h := by rw [div_div]
      _ ≤ Real.log ((T:ℝ) + 1) / G h := div_le_div_of_nonneg_right hlogT hGpos.le
      _ ≤ _ := log_div_G_le_Hs h T
  have hc : 0 < Real.log X / (20 * G h) := by positivity
  have hS' : (Real.log X / (20 * G h)) ^ 2 ≤ (pairSieve X h z hh y hy).selbergBoundingSum :=
    (pow_le_pow_left₀ hc.le hHs 2).trans hS
  have hdiv : (X:ℝ) / (pairSieve X h z hh y hy).selbergBoundingSum ≤
      400 * G h ^ 2 * X / Real.log X ^ 2 := by
    calc (X:ℝ) / (pairSieve X h z hh y hy).selbergBoundingSum
        ≤ (X:ℝ) / (Real.log X / (20 * G h)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hS'
      _ = _ := by field_simp; ring
  have hpairs' : (#{n ∈ Finset.range X | n.Prime ∧ (n + h).Prime} : ℝ) ≤
      (z:ℝ) + 1 + #{n ∈ Finset.range X | Nat.Coprime (sieveP z h) (n * (n + h))} := by
    exact_mod_cast pairs_le_sifted X h z
  have hz : (z:ℝ) ≤ y := Nat.floor_le (by linarith)
  have hy3 : y ^ 3 = (X:ℝ) ^ (3/5 : ℝ) := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hy35 : y ≤ (X:ℝ) ^ (3/5 : ℝ) := by
    rw [hydef]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have h1X : 1 ≤ (X:ℝ) ^ (3/5 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  linarith

end Vinogradov.MV
