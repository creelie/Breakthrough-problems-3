import Vinogradov.PV.PrimeSum
import Vinogradov.PV.Tools

/-!
# Prime sums on major arcs

For a primitive character `χ` modulo `q`, a modulus `0 < r < q`, an integer `c` and a real `θ`,
`∑_{A < p ≤ B} χ(p) e(pc/r) e(pθ)` is bounded by `C r B^{19/20} log (qr + 2) (2 + 2π|θ|B) / log A`
when `A ≥ max(2, r)`. The additive character `e(pc/r)` is expanded in Dirichlet characters `ψ`
modulo `r`; each `χψ` is a nonprincipal character modulo `qr` because `χ` is primitive and
`r < q`.
-/

namespace Vinogradov.PV

open Complex Finset

/-- A function on `ZMod r` bounded by `1` is, on units, a combination of Dirichlet characters
with coefficients of norm at most `1`. -/
theorem expand_units {r : ℕ} [NeZero r] (f : ZMod r → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ∃ w : DirichletCharacter ℂ r → ℂ, (∀ ψ, ‖w ψ‖ ≤ 1) ∧
      ∀ a : ZMod r, IsUnit a → f a = ∑ ψ : DirichletCharacter ℂ r, w ψ * ψ a := by
  have hφ : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have hφc : (r.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  refine ⟨fun ψ => (r.totient : ℂ)⁻¹ * ∑ b : (ZMod r)ˣ, ψ ((b : ZMod r)⁻¹) * f b, ?_, ?_⟩
  · intro ψ
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (r.totient : ℝ)⁻¹ * ‖∑ b : (ZMod r)ˣ, ψ ((b : ZMod r)⁻¹) * f b‖
        ≤ (r.totient : ℝ)⁻¹ * ∑ b : (ZMod r)ˣ, (1 : ℝ) := by
          gcongr
          refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          calc ‖ψ ((b : ZMod r)⁻¹)‖ * ‖f b‖ ≤ 1 * 1 :=
                mul_le_mul (DirichletCharacter.norm_le_one ψ _) (hf _) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = 1 := by
          rw [sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one,
            inv_mul_cancel₀ hφ.ne']
  · intro a ha
    obtain ⟨u, rfl⟩ := ha
    dsimp only
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    have key : ∀ b : (ZMod r)ˣ, ∑ ψ : DirichletCharacter ℂ r,
        (r.totient : ℂ)⁻¹ * (ψ ((b : ZMod r)⁻¹) * f b) * ψ u =
        if b = u then f u else 0 := by
      intro b
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ b.isUnit (u : ZMod r)
      calc ∑ ψ : DirichletCharacter ℂ r, (r.totient : ℂ)⁻¹ * (ψ ((b : ZMod r)⁻¹) * f b) * ψ u
          = (r.totient : ℂ)⁻¹ * f b *
              ∑ ψ : DirichletCharacter ℂ r, ψ ((b : ZMod r)⁻¹) * ψ u := by
            rw [mul_sum]; refine sum_congr rfl fun ψ _ => ?_; ring
        _ = if b = u then f u else 0 := by
            rw [h]
            by_cases hb : b = u
            · subst hb; simp only [↓reduceIte]; field_simp
            · have : (b : ZMod r) ≠ u := fun h' => hb (Units.ext h')
              simp [hb, this]
    rw [sum_congr rfl (fun b _ => key b), sum_ite_eq' univ u]
    simp

/-- `‖stdAddChar a‖ = 1`. -/
theorem norm_stdAddChar {r : ℕ} [NeZero r] (a : ZMod r) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- `stdAddChar (n c) = e(n c / r)`. -/
theorem stdAddChar_eq_e {r : ℕ} [NeZero r] (n : ℕ) (c : ℤ) :
    ZMod.stdAddChar ((n : ZMod r) * (c : ZMod r)) = e ((n : ℝ) * c / r) := by
  have h : ((n : ZMod r) * (c : ZMod r)) = (((n : ℤ) * c : ℤ) : ZMod r) := by push_cast; ring
  rw [h, ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- The product character `χψ` at level `qr`. -/
noncomputable def prodChar {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    DirichletCharacter ℂ (q * r) :=
  χ.changeLevel (Nat.dvd_mul_right q r) * ψ.changeLevel (Nat.dvd_mul_left r q)

theorem changeLevel_natCast {n m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ n) (hm : n ∣ m)
    {k : ℕ} (hk : IsUnit (k : ZMod m)) : χ.changeLevel hm k = χ k := by
  obtain ⟨u, hu⟩ := hk
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd χ hm u, hu, ZMod.cast_natCast hm]

theorem prodChar_apply {q r : ℕ} [NeZero q] [NeZero r] (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (n : ℕ) : prodChar χ ψ n = χ n * ψ n := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod (q * r))
  · rw [changeLevel_natCast χ _ hu, changeLevel_natCast ψ _ hu]
  · have h0 : (χ.changeLevel (Nat.dvd_mul_right q r)) n = 0 := MulChar.map_nonunit _ hu
    rw [h0, zero_mul]
    rw [ZMod.isUnit_iff_coprime] at hu
    by_cases hq : n.Coprime q
    · have hr : ¬ n.Coprime r := fun hr => hu (Nat.Coprime.mul_right hq hr)
      rw [← ZMod.isUnit_iff_coprime] at hr
      rw [MulChar.map_nonunit ψ hr, mul_zero]
    · rw [← ZMod.isUnit_iff_coprime] at hq
      rw [MulChar.map_nonunit χ hq, zero_mul]

/-- `χψ` is nonprincipal when `χ` is primitive modulo `q` and `0 < r < q`. -/
theorem prodChar_ne_one {q r : ℕ} [NeZero q] [NeZero r] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hrq : r < q) (ψ : DirichletCharacter ℂ r) : prodChar χ ψ ≠ 1 := by
  intro h
  have h' : χ.changeLevel (Nat.dvd_mul_right q r) = (ψ⁻¹).changeLevel (Nat.dvd_mul_left r q) := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hf := DirichletCharacter.factorsThrough_gcd χ (ψ⁻¹) h'
  have hc : χ.conductor ≤ q.gcd r := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hf)
  have hg : q.gcd r ≤ r := Nat.gcd_le_right _ (NeZero.pos r)
  rw [hχ] at hc
  omega

/-- **Twisted prime sums.** `‖∑_{A < p ≤ B} ξ(p) e(pθ)‖ ≤ C B^{19/20} log (m + 2) (2 + 2π|θ|B) /
log A` for nonprincipal `ξ` modulo `m` and `2 ≤ A ≤ B`. -/
theorem twisted_prime_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (ξ : DirichletCharacter ℂ m), ξ ≠ 1 →
      ∀ A B : ℕ, 2 ≤ A → A ≤ B → ∀ θ : ℝ,
        ‖∑ p ∈ Ioc A B with p.Prime, (ξ p : ℂ) * e (p * θ)‖ ≤
          C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) *
            (2 + 2 * Real.pi * |θ| * B) / Real.log A := by
  obtain ⟨C, hC, hCb⟩ := prime_sum_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro m _ ξ hξ A B hA hAB θ
  have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hLm : 0 ≤ Real.log (m + 2) := Real.log_nonneg (by linarith)
  set a : ℕ → ℂ := fun n => if n.Prime then (ξ n : ℂ) * Real.log n else 0 with ha
  set g : ℕ → ℂ := fun n => e (n * θ) / (Real.log n : ℂ) with hg
  set P : ℕ → ℂ := fun n => ∑ p ∈ Ioc 0 n with p.Prime, (ξ p : ℂ) * Real.log p with hP
  have hPb : ∀ n : ℕ, 1 ≤ n → n ≤ B →
      ‖P n‖ ≤ C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) := by
    intro n hn hnB
    have h := hCb m ξ hξ n (by exact_mod_cast hn)
    rw [Nat.floor_natCast] at h
    refine h.trans ?_
    gcongr
  -- partial sums of `a`
  have hpart : ∀ n, A ≤ n → ∑ k ∈ Ioc A n, a k = P n - P A := by
    intro n hn
    rw [hP]
    simp only [ha]
    rw [sum_filter, sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le A) hn]
    ring
  have hBd : ∀ n, A ≤ n → n ≤ B →
      ‖∑ k ∈ Ioc A n, a k‖ ≤ 2 * C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) := by
    intro n hn hnB
    rw [hpart n hn]
    calc _ ≤ ‖P n‖ + ‖P A‖ := norm_sub_le _ _
      _ ≤ C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) +
            C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) :=
          add_le_add (hPb n (by omega) hnB) (hPb A (by omega) hAB)
      _ = _ := by ring
  have habel := abel_bound a g hAB hBd
  -- the sum is `∑ a(n) g(n)`
  have hsum : ∑ p ∈ Ioc A B with p.Prime, (ξ p : ℂ) * e (p * θ) =
      ∑ n ∈ Ioc A B, a n * g n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    simp only [ha, hg]
    split_ifs with hp
    · have hl : (Real.log n : ℂ) ≠ 0 := by
        have : 0 < Real.log n := Real.log_pos (by exact_mod_cast hp.one_lt)
        exact_mod_cast this.ne'
      field_simp
    · simp
  rw [hsum]
  -- bounds on `g`
  have hgB : ‖g B‖ ≤ 1 / Real.log A := by
    simp only [hg]
    rw [norm_div, norm_e, Complex.norm_real, Real.norm_eq_abs]
    have hlB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith)
      (by exact_mod_cast hAB)
    rw [abs_of_pos (by linarith)]
    exact one_div_le_one_div_of_le hlogA hlB
  have hstep : ∀ n ∈ Ico A B, ‖g (n + 1) - g n‖ ≤
      2 * Real.pi * |θ| / Real.log A + (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) := by
    intro n hn
    obtain ⟨h1, _⟩ := mem_Ico.mp hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hA.trans h1
    have hln : 0 < Real.log n := Real.log_pos (by linarith)
    have hln1 : Real.log n ≤ Real.log (n + 1 : ℕ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have hlA : Real.log A ≤ Real.log (n + 1 : ℕ) :=
      Real.log_le_log (by linarith) (by push_cast; exact_mod_cast (h1.trans (Nat.le_succ n)))
    simp only [hg]
    have hid : e ((n + 1 : ℕ) * θ) / (Real.log (n + 1 : ℕ) : ℂ) - e (n * θ) / (Real.log n : ℂ) =
        (e ((n + 1 : ℕ) * θ) - e (n * θ)) / (Real.log (n + 1 : ℕ) : ℂ) +
          e (n * θ) * (((1 / Real.log (n + 1 : ℕ) - 1 / Real.log n : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have h := norm_e_sub ((n + 1 : ℕ) * θ) (n * θ)
      have hd : |((n + 1 : ℕ) : ℝ) * θ - n * θ| = |θ| := by push_cast; ring_nf
      rw [hd] at h
      calc ‖e ((n + 1 : ℕ) * θ) - e (n * θ)‖ / Real.log (n + 1 : ℕ)
          ≤ 2 * Real.pi * |θ| / Real.log (n + 1 : ℕ) := by gcongr
        _ ≤ 2 * Real.pi * |θ| / Real.log A := by gcongr
    · rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have : 1 / Real.log (n + 1 : ℕ) ≤ 1 / Real.log n := one_div_le_one_div_of_le hln hln1
      rw [abs_of_nonpos (by linarith)]
      linarith
  have htele : ∀ N, A ≤ N → ∑ n ∈ Ico A N, (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) =
      1 / Real.log A - 1 / Real.log N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih => rw [sum_Ico_succ_top hN, ih]; ring
  have hvar : ∑ n ∈ Ico A B, ‖g (n + 1) - g n‖ ≤
      (2 * Real.pi * |θ| * B + 1) / Real.log A := by
    calc _ ≤ ∑ n ∈ Ico A B, (2 * Real.pi * |θ| / Real.log A +
          (1 / Real.log n - 1 / Real.log (n + 1 : ℕ))) := sum_le_sum hstep
      _ = (B - A : ℕ) * (2 * Real.pi * |θ| / Real.log A) +
            (1 / Real.log A - 1 / Real.log B) := by
          rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, htele B hAB]
      _ ≤ (2 * Real.pi * |θ| * B + 1) / Real.log A := by
          have h1 : ((B - A : ℕ) : ℝ) ≤ B := by
            rw [Nat.cast_sub hAB]; linarith
          have h2 : 0 ≤ 1 / Real.log B := by
            have : 0 ≤ Real.log B := Real.log_nonneg (by
              have : (A : ℝ) ≤ B := by exact_mod_cast hAB
              linarith)
            positivity
          have h3 : 0 ≤ 2 * Real.pi * |θ| / Real.log A := by positivity
          have h4 : ((B - A : ℕ) : ℝ) * (2 * Real.pi * |θ| / Real.log A) ≤
              B * (2 * Real.pi * |θ| / Real.log A) := mul_le_mul_of_nonneg_right h1 h3
          rw [add_div]
          have h5 : (B : ℝ) * (2 * Real.pi * |θ| / Real.log A) =
              2 * Real.pi * |θ| * B / Real.log A := by ring
          linarith
  have hK : 0 ≤ 2 * C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) := by positivity
  calc _ ≤ 2 * C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) *
        (‖g B‖ + ∑ n ∈ Ico A B, ‖g (n + 1) - g n‖) := habel
    _ ≤ 2 * C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (m + 2) *
        (1 / Real.log A + (2 * Real.pi * |θ| * B + 1) / Real.log A) := by gcongr
    _ = _ := by field_simp; ring

/-- **Major arcs.** For `χ` primitive modulo `q`, `0 < r < q`, `c ∈ ℤ`, `θ ∈ ℝ` and
`max(2, r) ≤ A ≤ B`,
`‖∑_{A < p ≤ B} χ(p) e(pc/r) e(pθ)‖ ≤ C r B^{19/20} log (qr + 2) (2 + 2π|θ|B) / log A`. -/
theorem major_arc_prime_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ r : ℕ, 0 < r → r < q → ∀ c : ℤ, ∀ θ : ℝ, ∀ A B : ℕ, 2 ≤ A → r ≤ A → A ≤ B →
        ‖∑ p ∈ Ioc A B with p.Prime, (χ p : ℂ) * e (p * c / r) * e (p * θ)‖ ≤
          C * r * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (q * r + 2) *
            (2 + 2 * Real.pi * |θ| * B) / Real.log A := by
  obtain ⟨C, hC, hCb⟩ := twisted_prime_sum
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ r hr hrq c θ A B hA hrA hAB
  have : NeZero r := ⟨hr.ne'⟩
  obtain ⟨w, hw, hwf⟩ := expand_units (fun a : ZMod r => ZMod.stdAddChar (a * (c : ZMod r)))
    (fun a => (norm_stdAddChar _).le)
  have hunit : ∀ p ∈ Ioc A B, p.Prime → IsUnit (p : ZMod r) := by
    intro p hp hpp
    rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hpp]
    intro hdvd
    have := Nat.le_of_dvd hr hdvd
    have := (mem_Ioc.mp hp).1
    omega
  have hexp : ∑ p ∈ Ioc A B with p.Prime, (χ p : ℂ) * e (p * c / r) * e (p * θ) =
      ∑ ψ : DirichletCharacter ℂ r, w ψ *
        ∑ p ∈ Ioc A B with p.Prime, (prodChar χ ψ p : ℂ) * e (p * θ) := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun p hp => ?_
    have hp' := mem_filter.mp hp
    have h1 : e (p * c / r) = ∑ ψ : DirichletCharacter ℂ r, w ψ * ψ p := by
      rw [← stdAddChar_eq_e]
      exact hwf _ (hunit p hp'.1 hp'.2)
    rw [h1, mul_sum, sum_mul]
    refine sum_congr rfl fun ψ _ => ?_
    rw [prodChar_apply]
    ring
  rw [hexp]
  have hcard : (Fintype.card (DirichletCharacter ℂ r) : ℝ) ≤ r := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r]
    exact_mod_cast Nat.totient_le r
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  set T : ℝ := C * (B : ℝ) ^ (19 / 20 : ℝ) * Real.log (q * r + 2) *
    (2 + 2 * Real.pi * |θ| * B) / Real.log A with hT
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Real.log (q * r + 2) := Real.log_nonneg (by nlinarith)
    positivity
  have hterm : ∀ ψ : DirichletCharacter ℂ r,
      ‖w ψ * ∑ p ∈ Ioc A B with p.Prime, (prodChar χ ψ p : ℂ) * e (p * θ)‖ ≤ T := by
    intro ψ
    rw [norm_mul]
    have h := hCb (q * r) (prodChar χ ψ) (prodChar_ne_one hχ hrq ψ) A B hA hAB θ
    push_cast at h
    calc ‖w ψ‖ * _ ≤ 1 * T := mul_le_mul (hw ψ) h (norm_nonneg _) zero_le_one
      _ = T := one_mul T
  calc _ ≤ ∑ ψ : DirichletCharacter ℂ r,
        ‖w ψ * ∑ p ∈ Ioc A B with p.Prime, (prodChar χ ψ p : ℂ) * e (p * θ)‖ := norm_sum_le _ _
    _ ≤ ∑ ψ : DirichletCharacter ℂ r, T := sum_le_sum fun ψ _ => hterm ψ
    _ = Fintype.card (DirichletCharacter ℂ r) * T := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ r * T := by gcongr
    _ = _ := by rw [hT]; ring

end Vinogradov.PV
