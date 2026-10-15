import Vinogradov.PV.Gauss

/-!
# Pólya's expansion

For a primitive character `χ` mod `q`,
`‖∑_{n ≤ T} χ(n)‖ ≤ √q (B + 6)` as soon as every sum `∑_{m ≤ H} χ̄(m) e(mβ)/m` with
`2H ≤ q` has norm at most `B`.
-/

namespace Vinogradov.PV

open Finset Complex

theorem e_eq_exp_I (x : ℝ) : e x = Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
  unfold e; congr 1; push_cast; ring

/-- `|1 - e(-θ)| = 2|sin πθ| ≥ 4|θ|` for `|θ| ≤ 1/2`. -/
theorem norm_one_sub_e_ge {θ : ℝ} (h : |θ| ≤ 1 / 2) : 4 * |θ| ≤ ‖1 - e (-θ)‖ := by
  have hx : 2 * Real.pi * -θ / 2 = -(Real.pi * θ) := by ring
  rw [norm_sub_rev, e_eq_exp_I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_two, hx, Real.sin_neg, abs_neg]
  have hj : 2 / Real.pi * (Real.pi * |θ|) ≤ Real.sin (Real.pi * |θ|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos, abs_nonneg θ])
  have hs : Real.sin (Real.pi * |θ|) ≤ |Real.sin (Real.pi * θ)| := by
    rcases abs_cases θ with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact le_abs_self _
    · rw [h1, mul_neg, Real.sin_neg]; exact neg_le_abs _
  have h2 : 2 / Real.pi * (Real.pi * |θ|) = 2 * |θ| := by
    field_simp
  linarith

/-- `1/(1 - e(-θ)) = 1/(2πiθ) + O(1)` for `0 < |θ| ≤ 1/2`. -/
theorem inv_one_sub_e_sub_le {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ 1 / 2) :
    ‖1 / (1 - e (-θ)) - 1 / (2 * Real.pi * I * θ)‖ ≤ 3 := by
  have hθ : 0 < |θ| := abs_pos.2 h0
  have hw := norm_one_sub_e_ge h
  have hwpos : 0 < ‖1 - e (-θ)‖ := by linarith
  have hw0 : 1 - e (-θ) ≠ 0 := norm_pos_iff.1 hwpos
  set z : ℂ := 2 * Real.pi * I * θ with hzdef
  have hz : ‖z‖ = 2 * Real.pi * |θ| := by
    simp only [hzdef, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, mul_one, abs_of_pos Real.pi_pos]
  have hzpos : 0 < ‖z‖ := by rw [hz]; positivity
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  rcases le_or_gt (2 * Real.pi * |θ|) 1 with hsmall | hlarge
  · have hexp : e (-θ) = Complex.exp (-z) := by
      unfold e; congr 1; rw [hzdef]; push_cast; ring
    have key : 1 / (1 - e (-θ)) - 1 / z =
        (Complex.exp (-z) - 1 - (-z)) / ((1 - e (-θ)) * z) := by
      rw [div_sub_div _ _ hw0 hz0, hexp]
      congr 1
      ring
    rw [key, norm_div, norm_mul]
    have hnum : ‖Complex.exp (-z) - 1 - (-z)‖ ≤ ‖-z‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le (by rw [norm_neg, hz]; exact hsmall)
    rw [norm_neg, hz] at hnum
    rw [div_le_iff₀ (by positivity), hz]
    calc ‖Complex.exp (-z) - 1 - (-z)‖ ≤ (2 * Real.pi * |θ|) ^ 2 := hnum
      _ = (Real.pi / 2) * ((4 * |θ|) * (2 * Real.pi * |θ|)) := by ring
      _ ≤ 3 * (‖1 - e (-θ)‖ * (2 * Real.pi * |θ|)) := by
          apply mul_le_mul (by linarith [Real.pi_le_four])
            (mul_le_mul_of_nonneg_right hw (by positivity)) (by positivity) (by norm_num)
  · have h1 : 1 / ‖1 - e (-θ)‖ ≤ 1 / (4 * |θ|) := one_div_le_one_div_of_le (by positivity) hw
    have h2 : 1 / ‖z‖ ≤ 1 := by
      rw [hz, div_le_one (by positivity)]; linarith
    have h3 : 1 / (4 * |θ|) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_le_four, abs_nonneg θ]
    calc ‖1 / (1 - e (-θ)) - 1 / z‖ ≤ ‖1 / (1 - e (-θ))‖ + ‖1 / z‖ := norm_sub_le _ _
      _ = 1 / ‖1 - e (-θ)‖ + 1 / ‖z‖ := by rw [norm_div, norm_div, norm_one]
      _ ≤ 3 := by linarith

/-- The geometric sum `∑_{n ≤ T} e(nθ) = (e(Tθ) - 1)/(1 - e(-θ))`. -/
theorem sum_e_geom (θ : ℝ) (hw : 1 - e (-θ) ≠ 0) (T : ℕ) :
    ∑ n ∈ Ioc 0 T, e (n * θ) = (e (T * θ) - 1) / (1 - e (-θ)) := by
  induction T with
  | zero => simp [e_zero]
  | succ T ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le T), ih]
    have h1 : e (((T + 1 : ℕ) : ℝ) * θ) * e (-θ) = e ((T : ℝ) * θ) := by
      rw [← e_add]; congr 1; push_cast; ring
    rw [div_add' _ _ _ hw, div_left_inj' hw]
    linear_combination -h1

section Reindex

variable {q : ℕ} [NeZero q]

theorem sum_pos_valMinAbs (F : ZMod q → ℂ) :
    ∑ x ∈ univ.filter (fun x : ZMod q => 0 < x.valMinAbs), F x =
      ∑ m ∈ Ioc 0 (q / 2), F m := by
  refine sum_nbij' (fun x => x.valMinAbs.toNat) (fun m => (m : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have hle := ZMod.natAbs_valMinAbs_le x
    simp only [mem_Ioc]
    omega
  · intro m hm
    simp only [mem_Ioc] at hm
    simp only [mem_filter, mem_univ, true_and]
    rw [ZMod.valMinAbs_natCast_of_le_half hm.2]
    exact_mod_cast hm.1
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have h1 : ((x.valMinAbs.toNat : ℕ) : ℤ) = x.valMinAbs := Int.toNat_of_nonneg hx.le
    calc ((x.valMinAbs.toNat : ℕ) : ZMod q) = (((x.valMinAbs.toNat : ℕ) : ℤ) : ZMod q) := by
          push_cast; rfl
      _ = x := by rw [h1, ZMod.coe_valMinAbs]
  · intro m hm
    simp only [mem_Ioc] at hm
    simp only [ZMod.valMinAbs_natCast_of_le_half hm.2, Int.toNat_natCast]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have h1 : ((x.valMinAbs.toNat : ℕ) : ℤ) = x.valMinAbs := Int.toNat_of_nonneg hx.le
    congr 1
    calc x = (x.valMinAbs : ZMod q) := (ZMod.coe_valMinAbs x).symm
      _ = (((x.valMinAbs.toNat : ℕ) : ℤ) : ZMod q) := by rw [h1]
      _ = ((x.valMinAbs.toNat : ℕ) : ZMod q) := by push_cast; rfl

theorem valMinAbs_neg_natCast {m : ℕ} (hm : 2 * m < q) :
    (-(m : ZMod q)).valMinAbs = -(m : ℤ) := by
  have hval : (m : ZMod q).val = m := ZMod.val_natCast_of_lt (by omega)
  rw [ZMod.valMinAbs_neg_of_ne_half (by rw [hval]; omega),
    ZMod.valMinAbs_natCast_of_le_half (by omega)]

theorem sum_neg_valMinAbs (F : ZMod q → ℂ) :
    ∑ x ∈ univ.filter (fun x : ZMod q => x.valMinAbs < 0), F x =
      ∑ m ∈ Ioc 0 ((q - 1) / 2), F (-(m : ZMod q)) := by
  refine sum_nbij' (fun x => (-x.valMinAbs).toNat) (fun m => -(m : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have hmem := ZMod.valMinAbs_mem_Ioc x
    simp only [Set.mem_Ioc] at hmem
    simp only [mem_Ioc]
    omega
  · intro m hm
    simp only [mem_Ioc] at hm
    simp only [mem_filter, mem_univ, true_and]
    rw [valMinAbs_neg_natCast (by omega)]
    omega
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have h1 : (((-x.valMinAbs).toNat : ℕ) : ℤ) = -x.valMinAbs := Int.toNat_of_nonneg (by omega)
    calc -(((-x.valMinAbs).toNat : ℕ) : ZMod q)
        = -((((-x.valMinAbs).toNat : ℕ) : ℤ) : ZMod q) := by push_cast; rfl
      _ = x := by rw [h1, Int.cast_neg, neg_neg, ZMod.coe_valMinAbs]
  · intro m hm
    simp only [mem_Ioc] at hm
    simp only [valMinAbs_neg_natCast (show 2 * m < q by omega), neg_neg, Int.toNat_natCast]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    have h1 : (((-x.valMinAbs).toNat : ℕ) : ℤ) = -x.valMinAbs := Int.toNat_of_nonneg (by omega)
    congr 1
    calc x = (x.valMinAbs : ZMod q) := (ZMod.coe_valMinAbs x).symm
      _ = -((((-x.valMinAbs).toNat : ℕ) : ℤ) : ZMod q) := by rw [h1, Int.cast_neg, neg_neg]
      _ = -(((-x.valMinAbs).toNat : ℕ) : ZMod q) := by push_cast; rfl

end Reindex

/-- **Pólya's expansion.** -/
theorem polya_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {B : ℝ}
    (hB : ∀ H : ℕ, 2 * H ≤ q → ∀ β : ℝ, ‖∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * β) / m‖ ≤ B)
    (T : ℕ) :
    ‖∑ n ∈ Ioc 0 T, χ n‖ ≤ Real.sqrt q * (B + 6) := by
  classical
  have : Fact (1 < q) := ⟨by omega⟩
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar with hψdef
  have hχi := isPrimitive_inv hχ
  set τ := gaussSum χ⁻¹ ψ with hτdef
  have hτ : ‖τ‖ = Real.sqrt q := gaussSum_norm hχi
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
  have hB0 : 0 ≤ B := by
    have := hB 0 (by omega) 0
    simpa using this
  have hexp : ∀ a : ZMod q, χ a * τ = ∑ x, χ⁻¹ x * ψ (a * x) := by
    intro a
    have := gaussSum_mulShift_of_isPrimitive ψ hχi a
    rw [inv_inv] at this
    rw [hτdef, ← this]
    simp only [gaussSum, AddChar.mulShift_apply]
  set h : ZMod q → ℤ := fun x => x.valMinAbs with hh
  set θ : ZMod q → ℝ := fun x => (h x : ℝ) / q with hθ
  have hψe : ∀ (n : ℕ) (x : ZMod q), ψ (n * x) = e (n * θ x) := by
    intro n x
    have := stdAddChar_eq_e (r := q) n (h x)
    simp only [hh, ZMod.coe_valMinAbs] at this
    rw [hψdef, this]
    congr 1
    simp only [hθ, hh]
    ring
  have hθle : ∀ x, |θ x| ≤ 1 / 2 := by
    intro x
    have hmem := ZMod.valMinAbs_mem_Ioc x
    simp only [Set.mem_Ioc] at hmem
    have h1 : -(q : ℝ) < (h x : ℝ) * 2 := by exact_mod_cast hmem.1
    have h2 : (h x : ℝ) * 2 ≤ q := by exact_mod_cast hmem.2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hqpos]; linarith
    · rw [hθ, div_le_iff₀ hqpos]; linarith
  have hh0 : ∀ x, x ≠ 0 → h x ≠ 0 := fun x hx => (ZMod.valMinAbs_eq_zero x).not.2 hx
  have hθ0 : ∀ x, x ≠ 0 → θ x ≠ 0 := by
    intro x hx
    exact div_ne_zero (by exact_mod_cast hh0 x hx) hqpos.ne'
  set r : ZMod q → ℂ := fun x => 1 / (1 - e (-θ x)) - 1 / (2 * Real.pi * I * θ x) with hr
  have hrle : ∀ x, x ≠ 0 → ‖r x‖ ≤ 3 := fun x hx => inv_one_sub_e_sub_le (hθ0 x hx) (hθle x)
  set D : ZMod q → ℂ := fun x => χ⁻¹ x * (e (T * θ x) - 1) / (h x : ℂ) with hD
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hdec : ∀ x, χ⁻¹ x * ∑ n ∈ Ioc 0 T, ψ (n * x) =
      (q / (2 * Real.pi * I)) * D x + χ⁻¹ x * (e (T * θ x) - 1) * r x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [hD, MulChar.map_zero]
    · have hw : 1 - e (-θ x) ≠ 0 := by
        have := norm_one_sub_e_ge (hθle x)
        have hpos : 0 < |θ x| := abs_pos.2 (hθ0 x hx)
        exact norm_pos_iff.1 (by linarith)
      simp_rw [hψe]
      rw [sum_e_geom (θ x) hw T]
      have hhx : (h x : ℂ) ≠ 0 := by exact_mod_cast hh0 x hx
      have hsplit : 1 / (1 - e (-θ x)) = 1 / (2 * Real.pi * I * θ x) + r x := by
        simp only [hr]; ring
      have hinv : (1 : ℂ) / (2 * Real.pi * I * (θ x : ℂ)) =
          (q / (2 * Real.pi * I)) * (1 / (h x : ℂ)) := by
        simp only [hθ]
        push_cast
        field_simp
      rw [div_eq_mul_one_div (e (T * θ x) - 1), hsplit, hinv]
      simp only [hD]
      ring
  have hsumexp : (∑ n ∈ Ioc 0 T, χ n) * τ =
      (q / (2 * Real.pi * I)) * ∑ x, D x + ∑ x, χ⁻¹ x * (e (T * θ x) - 1) * r x := by
    rw [sum_mul]
    rw [sum_congr rfl fun (n : ℕ) _ => hexp (n : ZMod q)]
    rw [sum_comm]
    rw [sum_congr rfl fun x _ => (mul_sum (Ioc 0 T) (fun n : ℕ => ψ (n * x)) (χ⁻¹ x)).symm]
    rw [sum_congr rfl fun x _ => hdec x]
    rw [sum_add_distrib, mul_sum]
  -- the remainder
  have hrem : ‖∑ x, χ⁻¹ x * (e (T * θ x) - 1) * r x‖ ≤ 6 * q := by
    calc ‖∑ x, χ⁻¹ x * (e (T * θ x) - 1) * r x‖
        ≤ ∑ x : ZMod q, ‖χ⁻¹ x * (e (T * θ x) - 1) * r x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ZMod q, (6 : ℝ) := by
          refine sum_le_sum fun x _ => ?_
          by_cases hx : x = 0
          · subst hx; simp [MulChar.map_zero]
          · rw [norm_mul, norm_mul]
            have h1 : ‖χ⁻¹ x‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
            have h2 : ‖e (T * θ x) - 1‖ ≤ 2 := by
              calc ‖e (T * θ x) - 1‖ ≤ ‖e (T * θ x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                _ = 2 := by rw [norm_e, norm_one]; norm_num
            have h3 := hrle x hx
            calc ‖χ⁻¹ x‖ * ‖e (T * θ x) - 1‖ * ‖r x‖ ≤ 1 * 2 * 3 := by gcongr
              _ = 6 := by norm_num
      _ = 6 * q := by rw [sum_const, card_univ, ZMod.card]; simp [mul_comm]
  -- the main term
  have hmain : ‖∑ x, D x‖ ≤ 4 * B := by
    have hsplit1 : ∑ x, D x = ∑ x ∈ univ.filter (fun x : ZMod q => 0 < x.valMinAbs), D x +
        ∑ x ∈ univ.filter (fun x : ZMod q => ¬ 0 < x.valMinAbs), D x :=
      (sum_filter_add_sum_filter_not _ _ _).symm
    have hsplit2 : ∑ x ∈ univ.filter (fun x : ZMod q => ¬ 0 < x.valMinAbs), D x =
        ∑ x ∈ univ.filter (fun x : ZMod q => x.valMinAbs < 0), D x := by
      symm
      refine sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
      · simp only [mem_filter, mem_univ, true_and] at hx ⊢; omega
      · simp only [mem_filter, mem_univ, true_and, not_lt] at hx hx'
        have : x.valMinAbs = 0 := by omega
        simp [hD, hh, this]
    have hpos : ∑ x ∈ univ.filter (fun x : ZMod q => 0 < x.valMinAbs), D x =
        ∑ m ∈ Ioc 0 (q / 2), χ⁻¹ m * e (m * ((T : ℝ) / q)) / m -
          ∑ m ∈ Ioc 0 (q / 2), χ⁻¹ m * e (m * 0) / m := by
      rw [sum_pos_valMinAbs, ← sum_sub_distrib]
      refine sum_congr rfl fun m hm => ?_
      rw [mem_Ioc] at hm
      have hvm : (m : ZMod q).valMinAbs = m := ZMod.valMinAbs_natCast_of_le_half hm.2
      simp only [hD, hθ, hh, hvm, mul_zero, e_zero]
      have : e ((T : ℝ) * (((m : ℤ) : ℝ) / q)) = e ((m : ℝ) * (T / q)) := by
        congr 1; push_cast; ring
      rw [this]
      push_cast
      ring
    have hneg : ∑ x ∈ univ.filter (fun x : ZMod q => x.valMinAbs < 0), D x =
        -χ⁻¹ (-1) * (∑ m ∈ Ioc 0 ((q - 1) / 2), χ⁻¹ m * e (m * (-(T : ℝ) / q)) / m -
          ∑ m ∈ Ioc 0 ((q - 1) / 2), χ⁻¹ m * e (m * 0) / m) := by
      rw [sum_neg_valMinAbs, ← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [mem_Ioc] at hm
      have hvm : (-(m : ZMod q)).valMinAbs = -(m : ℤ) := valMinAbs_neg_natCast (by omega)
      have hχm : χ⁻¹ (-(m : ZMod q)) = χ⁻¹ (-1) * χ⁻¹ m := by
        rw [← map_mul, neg_one_mul]
      simp only [hD, hθ, hh, hvm, mul_zero, e_zero, hχm]
      have : e ((T : ℝ) * (((-(m : ℤ) : ℤ) : ℝ) / q)) = e ((m : ℝ) * (-(T : ℝ) / q)) := by
        congr 1; push_cast; ring
      rw [this]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      push_cast
      field_simp
    have hS : ∀ H : ℕ, 2 * H ≤ q → ∀ β : ℝ,
        ‖∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * β) / m - ∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * 0) / m‖ ≤ 2 * B := by
      intro H hH β
      calc _ ≤ ‖∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * β) / m‖ +
            ‖∑ m ∈ Ioc 0 H, χ⁻¹ m * e (m * 0) / m‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB H hH β) (hB H hH 0)
        _ = 2 * B := by ring
    rw [hsplit1, hsplit2, hpos, hneg]
    have h1 := hS (q / 2) (by omega) ((T : ℝ) / q)
    have h2 := hS ((q - 1) / 2) (by omega) (-(T : ℝ) / q)
    have hc : ‖-χ⁻¹ (-1)‖ ≤ 1 := by rw [norm_neg]; exact DirichletCharacter.norm_le_one _ _
    calc _ ≤ ‖∑ m ∈ Ioc 0 (q / 2), χ⁻¹ m * e (m * ((T : ℝ) / q)) / m -
            ∑ m ∈ Ioc 0 (q / 2), χ⁻¹ m * e (m * 0) / m‖ +
          ‖-χ⁻¹ (-1) * (∑ m ∈ Ioc 0 ((q - 1) / 2), χ⁻¹ m * e (m * (-(T : ℝ) / q)) / m -
            ∑ m ∈ Ioc 0 ((q - 1) / 2), χ⁻¹ m * e (m * 0) / m)‖ := norm_add_le _ _
      _ ≤ 2 * B + 1 * (2 * B) := by
          rw [norm_mul]
          gcongr
      _ = 4 * B := by ring
  -- assemble
  have hnorm : ‖∑ n ∈ Ioc 0 T, χ n‖ * Real.sqrt q ≤ q / (2 * Real.pi) * (4 * B) + 6 * q := by
    rw [← hτ, ← norm_mul, hsumexp]
    calc _ ≤ ‖(q / (2 * Real.pi * I)) * ∑ x, D x‖ +
          ‖∑ x, χ⁻¹ x * (e (T * θ x) - 1) * r x‖ := norm_add_le _ _
      _ ≤ q / (2 * Real.pi) * (4 * B) + 6 * q := by
          rw [norm_mul]
          have : ‖(q : ℂ) / (2 * Real.pi * I)‖ = q / (2 * Real.pi) := by
            rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast, norm_mul,
              Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          rw [this]
          gcongr
  have hfin : q / (2 * Real.pi) * (4 * B) + 6 * q ≤ q * (B + 6) := by
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have : q / (2 * Real.pi) * (4 * B) ≤ q * B := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hqpos.le hB0]
    linarith
  have : ‖∑ n ∈ Ioc 0 T, χ n‖ * Real.sqrt q ≤ Real.sqrt q * (B + 6) * Real.sqrt q := by
    calc _ ≤ q * (B + 6) := hnorm.trans hfin
      _ = (Real.sqrt q * Real.sqrt q) * (B + 6) := by rw [Real.mul_self_sqrt hqpos.le]
      _ = Real.sqrt q * (B + 6) * Real.sqrt q := by ring
  exact le_of_mul_le_mul_right this hsq

end Vinogradov.PV
