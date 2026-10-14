import Vinogradov.PV.Smooth

/-!
# The Gauss sum of a primitive character has absolute value `√q`

Parseval over the additive characters `x ↦ ψ(a x)`.
-/

namespace Vinogradov.PV

open Finset Complex ComplexConjugate

theorem gaussSum_norm_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  classical
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar q
  set τ := gaussSum χ ψ with hτ
  set G : ZMod q → ℂ := fun a => ∑ x, χ x * ψ (a * x) with hG
  have hGτ : ∀ a, G a = χ⁻¹ a * τ := fun a => by
    rw [hτ, ← gaussSum_mulShift_of_isPrimitive ψ hχ a]
    simp only [G, gaussSum, AddChar.mulShift_apply]
  set U : ℂ := ∑ x, χ x * conj (χ x) with hU
  have h1 : ∑ a, G a * conj (G a) = U * (τ * conj τ) := by
    simp_rw [hGτ, map_mul]
    rw [hU, sum_mul]
    refine sum_congr rfl fun a _ => ?_
    rw [← MulChar.star_apply' χ a, RCLike.star_def, Complex.conj_conj]
    ring
  have h2 : ∑ a, G a * conj (G a) = q * U := by
    calc ∑ a, G a * conj (G a)
        = ∑ a, ∑ x, ∑ y, χ x * conj (χ y) * ψ (a * (x - y)) := by
          refine sum_congr rfl fun a _ => ?_
          simp only [G, map_sum, map_mul]
          rw [Finset.sum_mul_sum]
          refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
          rw [← AddChar.map_neg_eq_conj, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
          ring
      _ = ∑ x, ∑ y, χ x * conj (χ y) * ∑ a, ψ (a * (x - y)) := by
          rw [sum_comm]
          refine sum_congr rfl fun x _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun y _ => ?_
          rw [mul_sum]
      _ = ∑ x, ∑ y, χ x * conj (χ y) * (if x - y = 0 then (q : ℂ) else 0) := by
          refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
          rw [AddChar.sum_mulShift _ hψ, ZMod.card]; push_cast; rfl
      _ = ∑ x, χ x * conj (χ x) * q := by
          refine sum_congr rfl fun x _ => ?_
          simp only [sub_eq_zero, mul_ite, mul_zero]
          rw [sum_ite_eq]
          simp
      _ = q * U := by rw [hU, mul_sum]; exact sum_congr rfl fun x _ => by ring
  have hUpos : U ≠ 0 := by
    have hU' : U = ((∑ x, Complex.normSq (χ x) : ℝ) : ℂ) := by
      rw [hU]; push_cast; exact sum_congr rfl fun x _ => Complex.mul_conj _
    rw [hU']
    have : (1 : ℝ) ≤ ∑ x, Complex.normSq (χ x) := by
      have := Finset.single_le_sum (f := fun x => Complex.normSq (χ x))
        (fun x _ => Complex.normSq_nonneg _) (mem_univ (1 : ZMod q))
      simpa using this
    exact_mod_cast (show (∑ x, Complex.normSq (χ x)) ≠ 0 by linarith)
  have h3 : τ * conj τ = q := by
    have := h1.symm.trans h2
    rw [mul_comm (q : ℂ) U] at this
    exact mul_left_cancel₀ hUpos this
  rw [Complex.mul_conj] at h3
  rw [Complex.sq_norm]
  exact_mod_cast h3

theorem gaussSum_norm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ = Real.sqrt q := by
  rw [← gaussSum_norm_sq hχ, Real.sqrt_sq (norm_nonneg _)]

theorem isPrimitive_inv {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact hχ

end Vinogradov.PV
