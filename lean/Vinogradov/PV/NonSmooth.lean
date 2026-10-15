import Vinogradov.PV.Twist

/-!
# Integers with a large prime factor

`gpf n` is the greatest prime factor of `n` (`0` for `n = 1`). An integer `n ≤ t` with
`gpf n > Y` is written uniquely as `n = p m` with `p = gpf n` prime and `gpf m ≤ p`. On a major
arc `α = b/r + β` the sum of `χ(n) e(nα)` over such `n` is controlled by the major-arc prime sums.
-/

namespace Vinogradov.PV

open Complex Finset

/-- The greatest prime factor (`0` for `n ≤ 1`). -/
def gpf (n : ℕ) : ℕ := n.primeFactors.sup id

theorem le_gpf {n p : ℕ} (hp : p ∈ n.primeFactors) : p ≤ gpf n :=
  le_sup (f := id) hp

theorem gpf_mem {n : ℕ} (h : n.primeFactors.Nonempty) : gpf n ∈ n.primeFactors := by
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ h id
  unfold gpf; rw [he]; exact hi

theorem gpf_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hpm : gpf m ≤ p) : gpf (p * m) = p := by
  unfold gpf
  rw [Nat.primeFactors_mul hp.ne_zero hm, hp.primeFactors, sup_union, sup_singleton]
  exact max_eq_left hpm

theorem gpf_mono {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) : gpf m ≤ gpf n :=
  sup_mono (Nat.primeFactors_mono hmn hn)

theorem nonempty_of_lt_gpf {n Y : ℕ} (h : Y < gpf n) : n.primeFactors.Nonempty := by
  by_contra hc
  rw [not_nonempty_iff_eq_empty] at hc
  unfold gpf at h; rw [hc, sup_empty] at h
  exact Nat.not_lt_zero _ h

/-- **Decomposition by the greatest prime factor.** -/
theorem sum_gpf (f : ℕ → ℂ) (Y t : ℕ) :
    ∑ n ∈ Ioc 0 t with Y < gpf n, f n =
      ∑ m ∈ Ioc 0 t, ∑ p ∈ Ioc (max Y (gpf m - 1)) (t / m) with p.Prime, f (p * m) := by
  rw [sum_sigma']
  symm
  refine sum_nbij' (fun x => x.2 * x.1) (fun n => ⟨n / gpf n, gpf n⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, p⟩ hx
    simp only [mem_sigma, mem_Ioc, mem_filter, max_lt_iff] at hx
    obtain ⟨⟨hm0, hmt⟩, ⟨⟨hYp, hgp⟩, hpt⟩, hp⟩ := hx
    have hgm : gpf m ≤ p := by omega
    have hg := gpf_mul hp (by omega) hgm
    simp only [mem_filter, mem_Ioc]
    refine ⟨⟨Nat.mul_pos hp.pos hm0, (Nat.le_div_iff_mul_le hm0).mp hpt⟩, ?_⟩
    rw [hg]; exact hYp
  · intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨hn0, hnt⟩, hY⟩ := hn
    have hne := nonempty_of_lt_gpf hY
    have hmem := gpf_mem hne
    rw [Nat.mem_primeFactors] at hmem
    obtain ⟨hp, hdvd, _⟩ := hmem
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hdiv : n / gpf n = k := Nat.div_eq_of_eq_mul_left hp.pos (by rw [mul_comm]; exact hk)
    simp only [mem_sigma, mem_filter, mem_Ioc, max_lt_iff]
    rw [hdiv]
    have hkn : k ≤ n := Nat.le_of_dvd hn0 (Dvd.intro_left (gpf n) hk.symm)
    have hgk : gpf k ≤ gpf n := gpf_mono (Dvd.intro_left (gpf n) hk.symm) (by omega)
    refine ⟨⟨hk0, by omega⟩, ⟨⟨hY, by omega⟩, ?_⟩, hp⟩
    rw [Nat.le_div_iff_mul_le hk0]
    calc gpf n * k = n := hk.symm
      _ ≤ t := hnt
  · rintro ⟨m, p⟩ hx
    simp only [mem_sigma, mem_filter, mem_Ioc, max_lt_iff] at hx
    obtain ⟨⟨hm0, _⟩, ⟨⟨_, hgp⟩, _⟩, hp⟩ := hx
    have hg := gpf_mul (m := m) hp (by omega) (by omega)
    simp only [hg, Nat.mul_div_cancel_left _ hp.pos]
  · intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨hn0, _⟩, hY⟩ := hn
    have hmem := gpf_mem (nonempty_of_lt_gpf hY)
    rw [Nat.mem_primeFactors] at hmem
    exact Nat.mul_div_cancel' hmem.2.1 |> fun h => by simpa [mul_comm] using h
  · intro x _
    rfl

/-- **Non-smooth part on a major arc.** For `χ` primitive modulo `q`, `0 < r < q`, `b ∈ ℤ`,
`β ∈ ℝ`, `2 ≤ Y`, `r ≤ Y`:
`‖∑_{n ≤ t, gpf n > Y} χ(n) e(n (b/r + β))‖ ≤ C r log (qr + 2) (2 + 2π|β|t) t / (Y^{1/20} log Y)`.
-/
theorem nonsmooth_major :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ r : ℕ, 0 < r → r < q → ∀ (b : ℤ) (β : ℝ) (Y t : ℕ), 2 ≤ Y → r ≤ Y →
        ‖∑ n ∈ Ioc 0 t with Y < gpf n, (χ n : ℂ) * e (n * (b / r + β))‖ ≤
          C * r * Real.log (q * r + 2) * (2 + 2 * Real.pi * |β| * t) * t /
            ((Y : ℝ) ^ (1 / 20 : ℝ) * Real.log Y) := by
  obtain ⟨C, hC, hCb⟩ := major_arc_prime_sum
  refine ⟨20 * C, by positivity, ?_⟩
  intro q _ χ hχ r hr hrq b β Y t hY hrY
  have hY' : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hLq : 0 ≤ Real.log (q * r + 2) := Real.log_nonneg (by nlinarith)
  set K : ℝ := C * r * Real.log (q * r + 2) * (2 + 2 * Real.pi * |β| * t) / Real.log Y with hK
  have hK0 : 0 ≤ K := by positivity
  rw [sum_gpf]
  -- each inner sum
  have hinner : ∀ m ∈ Ioc 0 t,
      ‖∑ p ∈ Ioc (max Y (gpf m - 1)) (t / m) with p.Prime,
          (χ (p * m : ℕ) : ℂ) * e ((p * m : ℕ) * (b / r + β))‖ ≤
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
      rw [if_pos hmY]
      have hrew : ∑ p ∈ Ioc A B with p.Prime,
          (χ (p * m : ℕ) : ℂ) * e ((p * m : ℕ) * (b / r + β)) =
          χ m * ∑ p ∈ Ioc A B with p.Prime,
            (χ p : ℂ) * e (p * ((m * b : ℤ) : ℝ) / r) * e (p * (m * β)) := by
        rw [mul_sum]
        refine sum_congr rfl fun p _ => ?_
        have h1 : e (((p * m : ℕ) : ℝ) * (b / r + β)) =
            e (p * ((m * b : ℤ) : ℝ) / r) * e (p * (m * β)) := by
          rw [← e_add]; congr 1; push_cast; field_simp
        rw [h1, Nat.cast_mul, map_mul]
        ring
      rw [hrew, norm_mul]
      have hχm : ‖(χ m : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ m
      have hA2 : 2 ≤ A := hY.trans (le_max_left _ _)
      have hrA : r ≤ A := hrY.trans (le_max_left _ _)
      have h := hCb q χ hχ r hr hrq (m * b) (m * β) A B hA2 hrA hAB
      have hBt : (B : ℝ) ≤ t / m := by
        rw [hB, le_div_iff₀ hm0']
        exact_mod_cast Nat.div_mul_le_self t m
      have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
      have hθ : 2 * Real.pi * |(m : ℝ) * β| * B ≤ 2 * Real.pi * |β| * t := by
        rw [abs_mul, abs_of_pos hm0']
        have : (m : ℝ) * B ≤ t := by
          have := (le_div_iff₀ hm0').mp hBt; linarith
        have hb0 : 0 ≤ 2 * Real.pi * |β| := by positivity
        calc 2 * Real.pi * ((m : ℝ) * |β|) * B = (2 * Real.pi * |β|) * (m * B) := by ring
          _ ≤ (2 * Real.pi * |β|) * t := mul_le_mul_of_nonneg_left this hb0
          _ = 2 * Real.pi * |β| * t := by ring
      have hlA : Real.log Y ≤ Real.log A :=
        Real.log_le_log (by linarith) (by exact_mod_cast le_max_left Y (gpf m - 1))
      have hpowB : (B : ℝ) ^ (19 / 20 : ℝ) ≤ ((t : ℝ) / m) ^ (19 / 20 : ℝ) :=
        Real.rpow_le_rpow hB0 hBt (by norm_num)
      calc ‖(χ m : ℂ)‖ * _ ≤ 1 * (C * r * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (q * r + 2) *
            (2 + 2 * Real.pi * |(m : ℝ) * β| * B) / Real.log A) := by
            refine mul_le_mul hχm ?_ (norm_nonneg _) zero_le_one
            convert h using 3 <;> push_cast <;> ring_nf
        _ ≤ C * r * ((t : ℝ) / m) ^ (19 / 20 : ℝ) * Real.log (q * r + 2) *
            (2 + 2 * Real.pi * |β| * t) / Real.log Y := by
            rw [one_mul]
            gcongr
        _ = K * (((t : ℝ) / m) ^ (19 / 20 : ℝ)) := by rw [hK]; ring
    · rw [not_le] at hAB
      rw [Ioc_eq_empty (by omega), filter_empty, sum_empty, norm_zero]
      split_ifs <;> [positivity; exact le_rfl]
  calc _ ≤ ∑ m ∈ Ioc 0 t, ‖∑ p ∈ Ioc (max Y (gpf m - 1)) (t / m) with p.Prime,
          (χ (p * m : ℕ) : ℂ) * e ((p * m : ℕ) * (b / r + β))‖ := norm_sum_le _ _
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
        rw [hK]; field_simp

end Vinogradov.PV
