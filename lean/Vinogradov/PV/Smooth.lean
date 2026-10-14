import Vinogradov.PV.NonSmooth

/-!
# Mertens' estimates and sums over smooth numbers

* `mertens_first`: `∑_{p ≤ n} log p / p ≤ log n + log 4`.
* `sum_inv_prime_le`: `∑_{p ≤ N} 1/p ≤ log log N + 10`.
* `smooth_sum_le`: the sum of `1/n` over `n ≤ H` with no prime factor above `Y` is at most
  `e^11 log Y`.
-/

namespace Vinogradov.PV

open Finset

/-- **Abel summation**, real form. -/
theorem abel_identity_real (a g : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Ioc M N, a n * g n =
      (∑ k ∈ Ioc M N, a k) * g N -
        ∑ n ∈ Ico M N, (∑ k ∈ Ioc M n, a k) * (g (n + 1) - g n) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [sum_Ioc_succ_top hMN, ih, sum_Ico_succ_top hMN, sum_Ioc_succ_top hMN]
    ring

theorem sum_Ico_telescope (G : ℕ → ℝ) {M N : ℕ} (h : M ≤ N) :
    ∑ n ∈ Ico M N, (G n - G (n + 1)) = G M - G N := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hMN ih => rw [sum_Ico_succ_top hMN, ih]; ring

/-- Legendre: `⌊n/p⌋ ≤ v_p(n!)`. -/
theorem factorization_factorial_ge {p n : ℕ} (hp : p.Prime) :
    n / p ≤ (n.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_succ_of_lt (Nat.lt_succ_self (Nat.log p n)))]
  have h1 : (1 : ℕ) ∈ Ico 1 (Nat.log p n + 1 + 1) := by simp
  calc n / p = n / p ^ 1 := by rw [pow_one]
    _ ≤ _ := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1

/-- **Mertens' first theorem** (upper bound). -/
theorem mertens_first (n : ℕ) :
    ∑ p ∈ Ioc 0 n with p.Prime, Real.log p / p ≤ Real.log n + Real.log 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Ioc_self, filter_empty, sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  set S := (Ioc 0 n).filter Nat.Prime with hS
  have hsupp : (n.factorial).factorization.support ⊆ S := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hdvd, -⟩ := hp
    rw [hS, mem_filter, mem_Ioc]
    exact ⟨⟨hpp.pos, hpp.dvd_factorial.1 hdvd⟩, hpp⟩
  have hlog : Real.log (n.factorial : ℕ) =
      ∑ p ∈ S, ((n.factorial).factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ hsupp]
    intro p _; simp
  have hlow : ∑ p ∈ S, ((n : ℝ) / p - 1) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
    rw [hlog]
    refine sum_le_sum fun p hp => ?_
    have hpp : p.Prime := (mem_filter.1 hp).2
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
    have h1 : ((n / p : ℕ) : ℝ) ≤ (n.factorial).factorization p := by
      exact_mod_cast factorization_factorial_ge hpp
    have h2 : (n : ℝ) / p - 1 < ((n / p : ℕ) : ℝ) := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.sub_one_lt_floor _
    linarith
  have hup : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    exact_mod_cast Nat.factorial_le_pow n
  have htheta : ∑ p ∈ S, Real.log p ≤ Real.log 4 * n := by
    have := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (Nat.cast_nonneg n)
    simpa [Chebyshev.theta, Nat.floor_natCast, hS] using this
  have hsplit : ∑ p ∈ S, ((n : ℝ) / p - 1) * Real.log p =
      n * ∑ p ∈ S, Real.log p / p - ∑ p ∈ S, Real.log p := by
    rw [mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun p _ => ?_; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) * ∑ p ∈ S, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left key hnpos

/-- `log n · (1/log n − 1/log(n+1)) ≤ 1/(n log n)` for `n ≥ 2`. -/
theorem log_mul_inv_sub_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log n * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) ≤ 1 / (n * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have huv : Real.log n ≤ Real.log (n + 1 : ℕ) :=
    Real.log_le_log hn0 (by exact_mod_cast Nat.le_succ n)
  have hv : 0 < Real.log (n + 1 : ℕ) := hu.trans_le huv
  have hdiff : Real.log (n + 1 : ℕ) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hn0.ne']
    calc Real.log ((n + 1 : ℕ) / (n : ℝ)) ≤ (n + 1 : ℕ) / (n : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / n := by push_cast; field_simp; ring
  have h1 : Real.log n * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) =
      (Real.log (n + 1 : ℕ) - Real.log n) / Real.log (n + 1 : ℕ) := by
    field_simp
  rw [h1]
  calc (Real.log (n + 1 : ℕ) - Real.log n) / Real.log (n + 1 : ℕ)
      ≤ (1 / n) / Real.log (n + 1 : ℕ) := by gcongr
    _ ≤ (1 / n) / Real.log n := by gcongr
    _ = 1 / (n * Real.log n) := by rw [div_div]

/-- **Mertens' second theorem** (upper bound). -/
theorem sum_inv_prime_le (N : ℕ) :
    ∑ p ∈ Ioc 0 N with p.Prime, (1 : ℝ) / p ≤ Real.log (Real.log N) + 10 := by
  rcases lt_or_ge N 2 with hN | hN
  · have : (Ioc 0 N).filter Nat.Prime = ∅ := by
      ext p
      simp only [mem_filter, mem_Ioc, notMem_empty, iff_false, not_and]
      intro h hp; have := hp.two_le; omega
    rw [this, sum_empty]
    interval_cases N <;> simp
  set a : ℕ → ℝ := fun n => if n.Prime then Real.log n / n else 0 with ha
  set g : ℕ → ℝ := fun n => 1 / Real.log n with hg
  set G : ℕ → ℝ := fun n => 1 / Real.log (max (n : ℝ) 2) with hG
  set A : ℕ → ℝ := fun n => ∑ k ∈ Ioc 1 n, a k with hA
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    simp only [ha]; split_ifs
    · exact div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
    · exact le_refl 0
  have hAle : ∀ n, A n ≤ Real.log n + Real.log 4 := fun n => by
    calc A n ≤ ∑ k ∈ Ioc 0 n, a k :=
          sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left zero_le_one) (fun k _ _ => ha0 k)
      _ = ∑ p ∈ Ioc 0 n with p.Prime, Real.log p / p := by rw [sum_filter]
      _ ≤ _ := mertens_first n
  have hA1 : A 1 = 0 := by simp [hA]
  have hag : ∀ n, a n * g n = if n.Prime then (1 : ℝ) / n else 0 := fun n => by
    simp only [ha, hg]; split_ifs with h
    · have : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.one_lt)
      field_simp
    · simp
  have hsum : ∑ p ∈ Ioc 0 N with p.Prime, (1 : ℝ) / p = ∑ n ∈ Ioc 1 N, a n * g n := by
    rw [sum_filter, ← sum_Ioc_consecutive _ zero_le_one (by omega : 1 ≤ N)]
    have h0 : ∑ n ∈ Ioc (0 : ℕ) 1, (if n.Prime then (1 : ℝ) / n else 0) = 0 := by
      rw [show (Ioc 0 1 : Finset ℕ) = {1} by decide, sum_singleton]; simp [Nat.not_prime_one]
    rw [h0, zero_add]
    exact sum_congr rfl fun n _ => (hag n).symm
  rw [hsum, abel_identity_real a g (by omega : 1 ≤ N)]
  show A N * g N - ∑ n ∈ Ico 1 N, A n * (g (n + 1) - g n) ≤ _
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have h1 : A N * g N ≤ 3 := by
    simp only [hg]
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    have := hAle N
    linarith
  have h2 : ∀ n ∈ Ico 1 N, -(A n * (g (n + 1) - g n)) ≤
      1 / (n * Real.log n) + Real.log 4 * (G n - G (n + 1)) := by
    intro n hn
    rcases (show n = 1 ∨ 2 ≤ n by simp only [mem_Ico] at hn; omega) with rfl | hn2
    · rw [hA1]; simp [hG]
    · have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlogn1 : Real.log n ≤ Real.log (n + 1 : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
      have hGn : G n = g n := by
        simp only [hG, hg, max_eq_left (show (2 : ℝ) ≤ n by exact_mod_cast hn2)]
      have hGn1 : G (n + 1) = g (n + 1) := by
        simp only [hG, hg, max_eq_left (show (2 : ℝ) ≤ (n + 1 : ℕ) by exact_mod_cast (by omega))]
      have hgdiff : 0 ≤ g n - g (n + 1) := by
        simp only [hg]; exact sub_nonneg.2 (one_div_le_one_div_of_le hlogn hlogn1)
      have hkey : Real.log n * (g n - g (n + 1)) ≤ 1 / (n * Real.log n) := by
        simp only [hg]; exact log_mul_inv_sub_le hn2
      calc -(A n * (g (n + 1) - g n)) = A n * (g n - g (n + 1)) := by ring
        _ ≤ (Real.log n + Real.log 4) * (g n - g (n + 1)) :=
          mul_le_mul_of_nonneg_right (hAle n) hgdiff
        _ = Real.log n * (g n - g (n + 1)) + Real.log 4 * (G n - G (n + 1)) := by
          rw [hGn, hGn1]; ring
        _ ≤ _ := by linarith [hkey]
  have h3 : ∑ n ∈ Ico 1 N, 1 / ((n : ℝ) * Real.log n) ≤ 3 + Real.log (Real.log N) := by
    calc ∑ n ∈ Ico 1 N, 1 / ((n : ℝ) * Real.log n)
        ≤ ∑ n ∈ Ioc 0 N, 1 / ((n : ℝ) * Real.log n) := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => ?_)
          · intro n hn; simp only [mem_Ico, mem_Ioc] at hn ⊢; omega
          · exact div_nonneg zero_le_one
              (mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n))
      _ ≤ _ := sum_inv_mul_log_le' N
  have h4 : ∑ n ∈ Ico 1 N, (G n - G (n + 1)) ≤ 1 / Real.log 2 := by
    rw [sum_Ico_telescope G (by omega : 1 ≤ N)]
    have hG1 : G 1 = 1 / Real.log 2 := by simp [hG]
    have hGN : 0 ≤ G N := by
      simp only [hG]
      exact div_nonneg zero_le_one (Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _)))
    linarith
  have h5 : -∑ n ∈ Ico 1 N, A n * (g (n + 1) - g n) ≤
      (3 + Real.log (Real.log N)) + Real.log 4 * (1 / Real.log 2) := by
    rw [← sum_neg_distrib]
    calc ∑ n ∈ Ico 1 N, -(A n * (g (n + 1) - g n))
        ≤ ∑ n ∈ Ico 1 N, (1 / (n * Real.log n) + Real.log 4 * (G n - G (n + 1))) :=
          sum_le_sum h2
      _ = ∑ n ∈ Ico 1 N, 1 / ((n : ℝ) * Real.log n) +
            Real.log 4 * ∑ n ∈ Ico 1 N, (G n - G (n + 1)) := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ _ := by
          gcongr
  have h6 : Real.log 4 * (1 / Real.log 2) = 2 := by rw [hl4]; field_simp; done
  linarith

/-- `n ↦ 1/n` as a monoid homomorphism `ℕ →* ℝ`. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_inv]

theorem sum_Ioc_inv_sub (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ k ∈ Ioc 1 Y, (1 / ((k : ℝ) - 1) - 1 / k) = 1 - 1 / Y := by
  induction Y, hY using Nat.le_induction with
  | base => simp
  | succ Y hY ih =>
    rw [sum_Ioc_succ_top hY, ih]
    have : (0 : ℝ) < Y := by exact_mod_cast hY
    push_cast
    rw [add_sub_cancel_right]
    ring

/-- **Sums over smooth numbers.** -/
theorem smooth_sum_le (H Y : ℕ) (hY : 2 ≤ Y) :
    ∑ n ∈ Ioc 0 H with gpf n ≤ Y, (1 : ℝ) / n ≤ Real.exp 11 * Real.log Y := by
  classical
  have hf : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf (Y + 1)
  set T := (Ioc 0 H).filter (fun n => gpf n ≤ Y) with hT
  have hTs : ∀ n ∈ T, n ∈ (Y + 1).smoothNumbers := by
    intro n hn
    rw [hT, mem_filter, mem_Ioc] at hn
    refine Nat.mem_smoothNumbers_of_primeFactors_subset (by omega) fun p hp => ?_
    rw [mem_range]
    have := le_gpf hp
    omega
  have step1 : ∑ n ∈ T, (1 : ℝ) / n =
      ∑ m ∈ T.subtype (· ∈ (Y + 1).smoothNumbers), invHom m := by
    rw [Finset.sum_subtype_eq_sum_filter, filter_true_of_mem hTs]
    simp [invHom]
  have step2 : ∑ m ∈ T.subtype (· ∈ (Y + 1).smoothNumbers), invHom m ≤
      ∏ p ∈ (Y + 1).primesBelow, (1 - invHom p)⁻¹ :=
    sum_le_hasSum _ (fun m _ => by simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]; positivity)
      hsum
  have hpb : ∀ p ∈ (Y + 1).primesBelow, p.Prime ∧ 2 ≤ p ∧ p ≤ Y := by
    intro p hp
    rw [Nat.primesBelow, mem_filter, mem_range] at hp
    exact ⟨hp.2, hp.2.two_le, by omega⟩
  have step3 : ∏ p ∈ (Y + 1).primesBelow, (1 - invHom p)⁻¹ ≤
      Real.exp (∑ p ∈ (Y + 1).primesBelow, 1 / ((p : ℝ) - 1)) := by
    rw [Real.exp_sum]
    refine prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨-, hp2, -⟩ := hpb p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]
      apply inv_nonneg.2
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ (by linarith)
    · obtain ⟨-, hp2, -⟩ := hpb p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have heq : (1 - invHom p)⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
        simp only [invHom, MonoidHom.coe_mk, OneHom.coe_mk]
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (p : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [heq]
      exact Real.add_one_le_exp _
  have hsub : (Y + 1).primesBelow ⊆ Ioc 1 Y := fun p hp => by
    obtain ⟨-, hp2, hpY⟩ := hpb p hp
    rw [mem_Ioc]; omega
  have hprimes : (Y + 1).primesBelow = (Ioc 0 Y).filter Nat.Prime := by
    ext p
    simp only [Nat.primesBelow, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨by omega, h2⟩
  have step4 : ∑ p ∈ (Y + 1).primesBelow, 1 / ((p : ℝ) - 1) ≤
      ∑ p ∈ Ioc 0 Y with p.Prime, (1 : ℝ) / p + 1 := by
    have hsplit : ∑ p ∈ (Y + 1).primesBelow, 1 / ((p : ℝ) - 1) =
        ∑ p ∈ (Y + 1).primesBelow, (1 : ℝ) / p +
          ∑ p ∈ (Y + 1).primesBelow, (1 / ((p : ℝ) - 1) - 1 / p) := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun p _ => ?_; ring
    have htail : ∑ p ∈ (Y + 1).primesBelow, (1 / ((p : ℝ) - 1) - 1 / p) ≤ 1 := by
      calc ∑ p ∈ (Y + 1).primesBelow, (1 / ((p : ℝ) - 1) - 1 / p)
          ≤ ∑ k ∈ Ioc 1 Y, (1 / ((k : ℝ) - 1) - 1 / k) := by
            refine sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
            rw [mem_Ioc] at hk
            have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
            rw [sub_nonneg]
            exact one_div_le_one_div_of_le (by linarith) (by linarith)
        _ = 1 - 1 / Y := sum_Ioc_inv_sub Y (by omega)
        _ ≤ 1 := by
            have : (0 : ℝ) ≤ 1 / Y := by positivity
            linarith
    have hfirst : ∑ p ∈ (Y + 1).primesBelow, (1 : ℝ) / p =
        ∑ p ∈ Ioc 0 Y with p.Prime, (1 : ℝ) / p := by rw [hprimes]
    rw [hsplit]
    linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hmert := sum_inv_prime_le Y
  calc ∑ n ∈ Ioc 0 H with gpf n ≤ Y, (1 : ℝ) / n
      = ∑ m ∈ T.subtype (· ∈ (Y + 1).smoothNumbers), invHom m := step1
    _ ≤ Real.exp (∑ p ∈ (Y + 1).primesBelow, 1 / ((p : ℝ) - 1)) := step2.trans step3
    _ ≤ Real.exp (Real.log (Real.log Y) + 11) := by
        apply Real.exp_le_exp.2
        linarith
    _ = Real.exp 11 * Real.log Y := by
        rw [Real.exp_add, Real.exp_log hlogY, mul_comm]

end Vinogradov.PV
