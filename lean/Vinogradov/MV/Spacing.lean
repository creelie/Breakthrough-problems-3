import Vinogradov.PV.Polya

/-!
# Spacing of the multiples of a well-approximated real number

For `|α - a/r| ≤ 1/r²` the points `kα`, `0 < |k| ≤ r/2`, stay at distance at least `1/(2r)` from
the integers. Hence `nint(hα) < t` holds for at most `(4H/r + 1)(4rt + 1)` of the `h ≤ H`, and
`∑_{h ≤ H} min(M, 1/nint(hα))² ≤ (4H/r + 1)(20 r M + 3 M²)`.
-/

namespace Vinogradov.MV

open Finset Vinogradov.PV

/-- The distance from `θ` to the nearest integer. -/
noncomputable def nint (θ : ℝ) : ℝ := |θ - round θ|

theorem nint_nonneg (θ : ℝ) : 0 ≤ nint θ := abs_nonneg _

theorem nint_le_half (θ : ℝ) : nint θ ≤ 1 / 2 := abs_sub_round θ

theorem nint_le (θ : ℝ) (z : ℤ) : nint θ ≤ |θ - z| := round_le θ z

theorem nint_neg (θ : ℝ) : nint (-θ) = nint θ := by
  apply le_antisymm
  · calc nint (-θ) ≤ |-θ - ((-round θ : ℤ) : ℝ)| := nint_le _ _
      _ = nint θ := by unfold nint; push_cast; rw [← abs_neg]; ring_nf
  · calc nint θ ≤ |θ - ((-round (-θ) : ℤ) : ℝ)| := nint_le _ _
      _ = nint (-θ) := by unfold nint; push_cast; rw [← abs_neg]; ring_nf

/-- **Spacing.** If `|α - a| ≤ 1/r²` with `r` the denominator of `a`, then `nint(kα) ≥ 1/(2r)`
for every integer `k ≠ 0` with `2|k| ≤ r`. -/
theorem nint_mul_ge {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) {k : ℤ} (hk : k ≠ 0)
    (hkr : 2 * |k| ≤ (a.den : ℤ)) : 1 / (2 * (a.den : ℝ)) ≤ nint (k * α) := by
  set r : ℕ := a.den with hr
  have hr0 : (0 : ℝ) < r := by rw [hr]; exact_mod_cast a.pos
  set z : ℤ := round ((k : ℝ) * α)
  -- `k a.num - z r ≠ 0`
  have hne : k * a.num - z * r ≠ 0 := by
    intro h
    have hdvd : (r : ℤ) ∣ k * a.num := ⟨z, by linarith⟩
    have hcop : IsCoprime (r : ℤ) a.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      have := a.reduced
      simpa [Int.gcd, hr] using this
    have hdk : (r : ℤ) ∣ k := hcop.dvd_of_dvd_mul_right hdvd
    have := Int.le_of_dvd (abs_pos.2 hk) ((dvd_abs _ _).2 hdk)
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast a.pos
    have : 0 < |k| := abs_pos.2 hk
    linarith
  have h1 : (1 : ℝ) ≤ |(k : ℝ) * a.num - z * r| := by
    have : (1 : ℤ) ≤ |k * a.num - z * r| := Int.one_le_abs hne
    exact_mod_cast this
  have ha : (a : ℝ) = a.num / r := by rw [Rat.cast_def]
  have hkr' : 2 * |(k : ℝ)| ≤ r := by exact_mod_cast hkr
  -- `|kα - z| ≥ |k a/r - z| - |k| |α - a| ≥ 1/r - 1/(2r)`
  have hsplit : (k : ℝ) * α - z = ((k : ℝ) * a.num - z * r) / r + k * (α - a) := by
    rw [ha]; field_simp; ring
  have h2 : 1 / (r : ℝ) ≤ |((k : ℝ) * a.num - z * r) / r| := by
    rw [abs_div, abs_of_pos hr0]; exact div_le_div_of_nonneg_right h1 hr0.le
  have h3 : |(k : ℝ) * (α - a)| ≤ 1 / (2 * r) := by
    rw [abs_mul]
    calc |(k : ℝ)| * |α - a| ≤ (r / 2) * (1 / (r : ℝ) ^ 2) :=
          mul_le_mul (by linarith) hα (abs_nonneg _) (by positivity)
      _ = 1 / (2 * r) := by field_simp
  have h4 : 1 / (r : ℝ) - 1 / (2 * r) ≤ |(k : ℝ) * α - z| := by
    rw [hsplit]
    have := abs_add_le (((k : ℝ) * a.num - z * r) / r + k * (α - a)) (-(k * (α - a)))
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  have h5 : 1 / (r : ℝ) - 1 / (2 * r) = 1 / (2 * r) := by field_simp; ring
  unfold nint; rw [← h5]; exact h4

theorem abs_sub_lt_one_of_floor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊x⌋₊ = ⌊y⌋₊) : |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

/-- **Counting in a block.** At most `4rt + 1` of `L` consecutive `k`, `2L ≤ r`, have
`nint(kα) < t`. -/
theorem card_block {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (k₀ L : ℕ)
    (hL : 2 * L ≤ a.den) {t : ℝ} (ht : 0 ≤ t) :
    (#{k ∈ Ico k₀ (k₀ + L) | nint (((k : ℕ) : ℝ) * α) < t} : ℝ) ≤ 4 * a.den * t + 1 := by
  set r : ℕ := a.den with hr
  have hr0 : (0 : ℝ) < r := by rw [hr]; exact_mod_cast a.pos
  set y : ℕ → ℝ := fun k => (k : ℝ) * α - round ((k : ℝ) * α) with hy
  set g : ℕ → ℕ := fun k => ⌊(y k + t) * (2 * r)⌋₊ with hg
  have hcard : #{k ∈ Ico k₀ (k₀ + L) | nint (((k : ℕ) : ℝ) * α) < t} ≤ #(range (⌊4 * r * t⌋₊ + 1)) := by
    apply card_le_card_of_injOn g
    · intro k hk
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hk
      simp only [coe_range, Set.mem_Iio, Nat.lt_succ_iff]
      apply Nat.floor_le_floor
      have : |y k| < t := hk.2
      rw [abs_lt] at this
      nlinarith
    · intro k hk k' hk' hkk
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at hk hk'
      by_contra hne
      have hyk : |y k| < t := hk.2
      have hyk' : |y k'| < t := hk'.2
      rw [abs_lt] at hyk hyk'
      have hlt := abs_sub_lt_one_of_floor_eq (by nlinarith) (by nlinarith) hkk
      rw [← sub_mul, add_sub_add_right_eq_sub, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * r)] at hlt
      have hlt' : |y k - y k'| < 1 / (2 * r) := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      -- spacing
      have hd : ((k : ℤ) - k') ≠ 0 := by omega
      have hdr : 2 * |(k : ℤ) - k'| ≤ (r : ℤ) := by
        have : |(k : ℤ) - k'| < L := by rw [abs_lt]; constructor <;> omega
        omega
      have hsp := nint_mul_ge hα hd hdr
      have hle : nint ((((k : ℤ) - k' : ℤ) : ℝ) * α) ≤ |y k - y k'| := by
        have := nint_le ((((k : ℤ) - k' : ℤ) : ℝ) * α)
          (round ((k : ℝ) * α) - round ((k' : ℝ) * α))
        simp only [hy]; push_cast at this ⊢
        calc _ ≤ _ := this
          _ = _ := by ring_nf
      linarith
  have h2 : (#(range (⌊4 * r * t⌋₊ + 1)) : ℝ) ≤ 4 * r * t + 1 := by
    rw [card_range]; push_cast
    have := Nat.floor_le (show 0 ≤ 4 * (r : ℝ) * t by positivity)
    linarith
  calc (#{k ∈ Ico k₀ (k₀ + L) | nint (((k : ℕ) : ℝ) * α) < t} : ℝ)
      ≤ #(range (⌊4 * r * t⌋₊ + 1)) := by exact_mod_cast hcard
    _ ≤ _ := h2

/-- **Counting.** For `r ≥ 2`, at most `(4H/r + 1)(4rt + 1)` of the `h ≤ H` have `nint(hα) < t`. -/
theorem card_Icc {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den) (H : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (#{h ∈ Icc 1 H | nint (((h : ℕ) : ℝ) * α) < t} : ℝ) ≤ (4 * H / a.den + 1) * (4 * a.den * t + 1) := by
  set r : ℕ := a.den with hrdef
  set L : ℕ := r / 2 with hL
  have hL1 : 1 ≤ L := by omega
  have hL2 : 2 * L ≤ r := by omega
  have hmaps : Set.MapsTo (fun h => (h - 1) / L) ↑({h ∈ Icc 1 H | nint (((h : ℕ) : ℝ) * α) < t})
      ↑(range (H / L + 1)) := by
    intro h hh
    simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hh
    simp only [coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (by omega)
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hfib : ∀ b ∈ range (H / L + 1),
      (#{h ∈ {h ∈ Icc 1 H | nint (((h : ℕ) : ℝ) * α) < t} | (h - 1) / L = b} : ℝ) ≤ 4 * r * t + 1 := by
    intro b _
    refine le_trans ?_ (card_block hα (b * L + 1) L hL2 ht)
    gcongr
    intro h hh
    simp only [mem_filter, mem_Icc] at hh
    simp only [mem_filter, mem_Ico]
    refine ⟨⟨?_, ?_⟩, hh.1.2⟩
    · have := Nat.div_mul_le_self (h - 1) L
      rw [hh.2] at this; omega
    · have := Nat.lt_div_mul_add (a := h - 1) (b := L) (by omega)
      rw [hh.2] at this; omega
  calc ∑ b ∈ range (H / L + 1), (#{h ∈ {h ∈ Icc 1 H | nint (((h : ℕ) : ℝ) * α) < t} | (h - 1) / L = b} : ℝ)
      ≤ ∑ _b ∈ range (H / L + 1), (4 * (r : ℝ) * t + 1) := sum_le_sum hfib
    _ = ((H / L : ℕ) + 1) * (4 * r * t + 1) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (4 * H / r + 1) * (4 * r * t + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply add_le_add_left
        have hr0 : (0 : ℝ) < r := by positivity
        have hLr : (r : ℝ) ≤ 4 * L := by
          have : r ≤ 4 * L := by omega
          exact_mod_cast this
        calc ((H / L : ℕ) : ℝ) ≤ (H : ℝ) / L := Nat.cast_div_le
          _ ≤ 4 * H / r := by
            rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith [(H.cast_nonneg : (0 : ℝ) ≤ H)]

/-- `min(M, 1/nint θ)`, equal to `M` at the integers. -/
noncomputable def wt (M θ : ℝ) : ℝ := if nint θ < 1 / M then M else 1 / nint θ

theorem wt_nonneg {M : ℝ} (hM : 0 ≤ M) (θ : ℝ) : 0 ≤ wt M θ := by
  unfold wt; split_ifs
  · exact hM
  · exact div_nonneg zero_le_one (nint_nonneg θ)

theorem wt_le {M : ℝ} (hM : 0 < M) (θ : ℝ) : wt M θ ≤ M := by
  unfold wt; split_ifs with h
  · exact le_rfl
  · push_neg at h
    have h0 : 0 < 1 / M := by positivity
    rw [div_le_iff₀ (h0.trans_le h)]
    rw [div_le_iff₀ hM] at h; linarith

theorem wt_neg (M θ : ℝ) : wt M (-θ) = wt M θ := by unfold wt; rw [nint_neg]

theorem one_div_le_wt {M θ : ℝ} (hM : 0 < M) (h : 1 / M ≤ nint θ) : wt M θ = 1 / nint θ := by
  unfold wt; rw [if_neg (not_lt.2 h)]

/-- **Layer cake.** For `M ≤ 2^K`,
`wt(θ)² ≤ M² [nint θ < 1/M] + ∑_{1 ≤ k ≤ K} 4M² 4^{-k} [nint θ < 2^k/M]`. -/
theorem wt_sq_le {M : ℝ} (hM : 0 < M) (K : ℕ) (hK : M ≤ 2 ^ K) (θ : ℝ) :
    wt M θ ^ 2 ≤ M ^ 2 * (if nint θ < 1 / M then 1 else 0) +
      ∑ k ∈ Icc 1 K, 4 * M ^ 2 * (1 / 4) ^ k * (if nint θ < 2 ^ k / M then 1 else 0) := by
  have hterm : ∀ k ∈ Icc 1 K,
      0 ≤ 4 * M ^ 2 * (1 / 4 : ℝ) ^ k * (if nint θ < 2 ^ k / M then 1 else 0) := by
    intro k _; split_ifs <;> positivity
  by_cases h : nint θ < 1 / M
  · rw [if_pos h, wt, if_pos h, mul_one]
    have := sum_nonneg hterm
    linarith
  · push_neg at h
    rw [if_neg (not_lt.2 h), mul_zero, zero_add, one_div_le_wt hM h]
    set u := nint θ with hu
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) h
    have hex : ∃ k : ℕ, u < 2 ^ k / M := by
      refine ⟨K, ?_⟩
      have : (1 : ℝ) ≤ 2 ^ K / M := by rw [le_div_iff₀ hM]; linarith
      have := nint_le_half θ
      linarith
    classical
    set j := Nat.find hex with hj
    have hjspec : u < 2 ^ j / M := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hjspec
      linarith
    have hjK : j ≤ K := by
      apply Nat.find_min'
      have : (1 : ℝ) ≤ 2 ^ K / M := by rw [le_div_iff₀ hM]; linarith
      have := nint_le_half θ
      linarith
    have hjm : ¬ u < 2 ^ (j - 1) / M := Nat.find_min hex (by omega)
    push_neg at hjm
    have hmem : j ∈ Icc 1 K := mem_Icc.2 ⟨by omega, hjK⟩
    refine le_trans ?_ (single_le_sum hterm hmem)
    rw [if_pos hjspec, mul_one]
    have hpow : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2pos : (0 : ℝ) < 2 ^ (j - 1) := by positivity
    -- `1/u ≤ M / 2^(j-1)`
    have hinv : 1 / u ≤ M / 2 ^ (j - 1) := by
      rw [div_le_div_iff₀ hu0 h2pos, one_mul]
      rw [div_le_iff₀ hM] at hjm; linarith
    have hq : (4 : ℝ) * M ^ 2 * (1 / 4) ^ j = (M / 2 ^ (j - 1)) ^ 2 := by
      have h4 : (4 : ℝ) ^ j = (2 ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [one_div_pow, h4, hpow]; field_simp; ring
    rw [hq]
    exact pow_le_pow_left₀ (by positivity) hinv 2

theorem geom_half (K : ℕ) : ∑ k ∈ Icc 1 K, (1 / 2 : ℝ) ^ k ≤ 1 := by
  have := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 1) (n := K + 1)
    (by norm_num) (by norm_num)
  have hI : Icc 1 K = Ico 1 (K + 1) := rfl
  rw [hI]; norm_num at this ⊢; linarith

theorem geom_quarter (K : ℕ) : ∑ k ∈ Icc 1 K, (1 / 4 : ℝ) ^ k ≤ 1 / 3 := by
  have := geom_sum_Ico_le_of_lt_one (x := (1 / 4 : ℝ)) (m := 1) (n := K + 1)
    (by norm_num) (by norm_num)
  have hI : Icc 1 K = Ico 1 (K + 1) := rfl
  rw [hI]; norm_num at this ⊢; linarith

/-- **Second moment.** `∑_{h ≤ H} wt(hα)² ≤ (4H/r + 1)(20rM + 3M²)` for `r ≥ 2`. -/
theorem sum_wt_sq_le {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den)
    (H : ℕ) {M : ℝ} (hM : 0 < M) :
    ∑ h ∈ Icc 1 H, wt M ((h : ℝ) * α) ^ 2 ≤
      (4 * H / a.den + 1) * (20 * a.den * M + 3 * M ^ 2) := by
  set r : ℕ := a.den with hrdef
  set A : ℝ := 4 * H / r + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  set K : ℕ := ⌈M⌉₊ with hKdef
  have hK : M ≤ 2 ^ K := by
    calc M ≤ K := Nat.le_ceil M
      _ ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hcnt : ∀ t : ℝ, 0 ≤ t →
      ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < t then (1 : ℝ) else 0) ≤ A * (4 * r * t + 1) := by
    intro t ht
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    exact card_Icc hα hr H ht
  calc ∑ h ∈ Icc 1 H, wt M ((h : ℝ) * α) ^ 2
      ≤ ∑ h ∈ Icc 1 H, (M ^ 2 * (if nint ((h : ℝ) * α) < 1 / M then 1 else 0) +
        ∑ k ∈ Icc 1 K, 4 * M ^ 2 * (1 / 4) ^ k *
          (if nint ((h : ℝ) * α) < 2 ^ k / M then 1 else 0)) :=
        sum_le_sum fun h _ => wt_sq_le hM K hK _
    _ = M ^ 2 * ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < 1 / M then (1 : ℝ) else 0) +
        ∑ k ∈ Icc 1 K, 4 * M ^ 2 * (1 / 4) ^ k *
          ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < 2 ^ k / M then (1 : ℝ) else 0) := by
        rw [sum_add_distrib, ← mul_sum, sum_comm]
        congr 1
        apply sum_congr rfl; intro k _; rw [mul_sum]
    _ ≤ M ^ 2 * (A * (4 * r * (1 / M) + 1)) +
        ∑ k ∈ Icc 1 K, 4 * M ^ 2 * (1 / 4) ^ k * (A * (4 * r * (2 ^ k / M) + 1)) := by
        gcongr with k _
        · exact hcnt _ (by positivity)
        · exact hcnt _ (by positivity)
    _ = A * (4 * r * M + M ^ 2) +
        ∑ k ∈ Icc 1 K, A * (16 * r * M * (1 / 2 : ℝ) ^ k + 4 * M ^ 2 * (1 / 4 : ℝ) ^ k) := by
        congr 1
        · field_simp
        · apply sum_congr rfl; intro k _
          have h2 : (2 : ℝ) ^ k * (1 / 4) ^ k = (1 / 2) ^ k := by rw [← mul_pow]; norm_num
          rw [← h2]; field_simp; ring
    _ = A * (4 * r * M + M ^ 2 + 16 * r * M * ∑ k ∈ Icc 1 K, (1 / 2 : ℝ) ^ k +
        4 * M ^ 2 * ∑ k ∈ Icc 1 K, (1 / 4 : ℝ) ^ k) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]; ring
    _ ≤ A * (4 * r * M + M ^ 2 + 16 * r * M * 1 + 4 * M ^ 2 * (1 / 3)) := by
        gcongr
        · exact geom_half K
        · exact geom_quarter K
    _ ≤ A * (20 * r * M + 3 * M ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hA0; nlinarith

/-- **Layer cake, first moment.** For `M ≤ 2^K`,
`wt(θ) ≤ M [nint θ < 1/M] + ∑_{1 ≤ k ≤ K} 2M 2^{-k} [nint θ < 2^k/M]`. -/
theorem wt_le_layer {M : ℝ} (hM : 0 < M) (K : ℕ) (hK : M ≤ 2 ^ K) (θ : ℝ) :
    wt M θ ≤ M * (if nint θ < 1 / M then 1 else 0) +
      ∑ k ∈ Icc 1 K, 2 * M * (1 / 2) ^ k * (if nint θ < 2 ^ k / M then 1 else 0) := by
  have hterm : ∀ k ∈ Icc 1 K,
      0 ≤ 2 * M * (1 / 2 : ℝ) ^ k * (if nint θ < 2 ^ k / M then 1 else 0) := by
    intro k _; split_ifs <;> positivity
  by_cases h : nint θ < 1 / M
  · rw [if_pos h, wt, if_pos h, mul_one]
    have := sum_nonneg hterm
    linarith
  · push_neg at h
    rw [if_neg (not_lt.2 h), mul_zero, zero_add, one_div_le_wt hM h]
    set u := nint θ with hu
    have hu0 : 0 < u := lt_of_lt_of_le (by positivity) h
    have hex : ∃ k : ℕ, u < 2 ^ k / M := by
      refine ⟨K, ?_⟩
      have : (1 : ℝ) ≤ 2 ^ K / M := by rw [le_div_iff₀ hM]; linarith
      have := nint_le_half θ
      linarith
    classical
    set j := Nat.find hex with hj
    have hjspec : u < 2 ^ j / M := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hjspec
      linarith
    have hjK : j ≤ K := by
      apply Nat.find_min'
      have : (1 : ℝ) ≤ 2 ^ K / M := by rw [le_div_iff₀ hM]; linarith
      have := nint_le_half θ
      linarith
    have hjm : ¬ u < 2 ^ (j - 1) / M := Nat.find_min hex (by omega)
    push_neg at hjm
    have hmem : j ∈ Icc 1 K := mem_Icc.2 ⟨by omega, hjK⟩
    refine le_trans ?_ (single_le_sum hterm hmem)
    rw [if_pos hjspec, mul_one]
    have hpow : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2pos : (0 : ℝ) < 2 ^ (j - 1) := by positivity
    have hinv : 1 / u ≤ M / 2 ^ (j - 1) := by
      rw [div_le_div_iff₀ hu0 h2pos, one_mul]
      rw [div_le_iff₀ hM] at hjm; linarith
    have hq : (2 : ℝ) * M * (1 / 2) ^ j = M / 2 ^ (j - 1) := by
      rw [one_div_pow, hpow]; field_simp
    rw [hq]; exact hinv

/-- **First moment.** `∑_{h ≤ H} wt(hα) ≤ (4H/r + 1)(3M + 4r + 8rK)` for `r ≥ 2`, `M ≤ 2^K`. -/
theorem sum_wt_le {α : ℝ} {a : ℚ} (hα : |α - a| ≤ 1 / (a.den : ℝ) ^ 2) (hr : 2 ≤ a.den)
    (H : ℕ) {M : ℝ} (hM : 0 < M) (K : ℕ) (hK : M ≤ 2 ^ K) :
    ∑ h ∈ Icc 1 H, wt M ((h : ℝ) * α) ≤
      (4 * H / a.den + 1) * (3 * M + 4 * a.den + 8 * a.den * K) := by
  set r : ℕ := a.den with hrdef
  set A : ℝ := 4 * H / r + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hcnt : ∀ t : ℝ, 0 ≤ t →
      ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < t then (1 : ℝ) else 0) ≤ A * (4 * r * t + 1) := by
    intro t ht
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    exact card_Icc hα hr H ht
  calc ∑ h ∈ Icc 1 H, wt M ((h : ℝ) * α)
      ≤ ∑ h ∈ Icc 1 H, (M * (if nint ((h : ℝ) * α) < 1 / M then 1 else 0) +
        ∑ k ∈ Icc 1 K, 2 * M * (1 / 2) ^ k *
          (if nint ((h : ℝ) * α) < 2 ^ k / M then 1 else 0)) :=
        sum_le_sum fun h _ => wt_le_layer hM K hK _
    _ = M * ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < 1 / M then (1 : ℝ) else 0) +
        ∑ k ∈ Icc 1 K, 2 * M * (1 / 2) ^ k *
          ∑ h ∈ Icc 1 H, (if nint ((h : ℝ) * α) < 2 ^ k / M then (1 : ℝ) else 0) := by
        rw [sum_add_distrib, ← mul_sum, sum_comm]
        congr 1
        apply sum_congr rfl; intro k _; rw [mul_sum]
    _ ≤ M * (A * (4 * r * (1 / M) + 1)) +
        ∑ k ∈ Icc 1 K, 2 * M * (1 / 2) ^ k * (A * (4 * r * (2 ^ k / M) + 1)) := by
        gcongr with k _
        · exact hcnt _ (by positivity)
        · exact hcnt _ (by positivity)
    _ = A * (4 * r + M) + ∑ k ∈ Icc 1 K, A * (8 * r + 2 * M * (1 / 2 : ℝ) ^ k) := by
        congr 1
        · field_simp
        · apply sum_congr rfl; intro k _
          have h2 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
          have h3 : 2 * M * (1 / 2 : ℝ) ^ k * (A * (4 * r * (2 ^ k / M) + 1)) =
              8 * r * A * (2 ^ k * (1 / 2) ^ k) + A * (2 * M * (1 / 2) ^ k) := by
            field_simp; ring
          rw [h3, h2]; ring
    _ = A * (4 * r + M + 8 * r * K + 2 * M * ∑ k ∈ Icc 1 K, (1 / 2 : ℝ) ^ k) := by
        rw [← mul_sum, sum_add_distrib, sum_const, Nat.card_Icc, ← mul_sum, nsmul_eq_mul]
        push_cast; ring
    _ ≤ A * (4 * r + M + 8 * r * K + 2 * M * 1) := by
        gcongr; exact geom_half K
    _ = A * (3 * M + 4 * r + 8 * r * K) := by ring

end Vinogradov.MV
