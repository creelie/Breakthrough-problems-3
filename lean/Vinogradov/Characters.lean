import Mathlib
import Vinogradov.Riesz

/-!
# The indicator of primitive roots as a combination of Dirichlet characters

Let `p` be prime, `N = p - 1`, `g` a generator of `(ZMod p)ˣ` and `χ₁` the Dirichlet character
with `χ₁(g) = exp (2πi/N)`. For every natural number `n`,
`[n is a primitive root mod p] = ∑_{d ∣ N} (μ(d)/d) ∑_{m < d} χ₁^{m N/d}(n)`.
The term `m = 0` is the principal character and every other term is nonprincipal.
-/

namespace Vinogradov.Characters

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt LSeries.notation

variable {p : ℕ} [Fact p.Prime]

/-- A generator of `(ZMod p)ˣ` and a character sending it to a primitive `(p-1)`-th root of
unity. -/
structure Setup (p : ℕ) [Fact p.Prime] where
  g : (ZMod p)ˣ
  hg : ∀ x, x ∈ Subgroup.zpowers g
  ζ : ℂ
  hζ : IsPrimitiveRoot ζ (p - 1)
  χ : DirichletCharacter ℂ p
  hχ : χ (g : ZMod p) = ζ

theorem sub_one_pos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt

theorem exists_setup : Nonempty (Setup p) := by
  have hcyc : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hN : p - 1 ≠ 0 := (sub_one_pos (p := p)).ne'
  have hζ := Complex.isPrimitiveRoot_exp (p - 1) hN
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (p - 1 : ℕ))
  set u : ℂˣ := (hζ.isUnit hN).unit
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hu : orderOf u = p - 1 := by
    rw [← orderOf_units]
    simp only [u, IsUnit.unit_spec]
    exact hζ.eq_orderOf.symm
  let f : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg (g' := u) (by rw [hu, hord])
  refine ⟨⟨g, hg, ζ, hζ, MulChar.ofUnitHom f, ?_⟩⟩
  rw [MulChar.ofUnitHom_coe]
  simp [f, u, monoidHomOfForallMemZpowers_apply_gen]

/-- `∑_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (μ d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' : ((∑ d ∈ n.divisors, μ d : ℤ) : ℂ) = ((if n = 1 then 1 else 0 : ℤ) : ℂ) := by
    rw [h]
  push_cast at h'
  rw [h']

/-- The values of the powers of `χ` at a unit `g^k`. -/
theorem pow_apply_gen_pow (S : Setup p) (j k : ℕ) :
    (S.χ ^ j) ((S.g ^ k : (ZMod p)ˣ) : ZMod p) = S.ζ ^ (k * j) := by
  rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow, S.hχ, ← pow_mul]

/-- The geometric sum over a primitive `d`-th root of unity. -/
theorem sum_range_pow_root (S : Setup p) {d : ℕ} (hd : d ∈ (p - 1).divisors) (k : ℕ) :
    ∑ m ∈ range d, S.ζ ^ (k * (m * ((p - 1) / d))) = if d ∣ k then (d : ℂ) else 0 := by
  have hdN : d ∣ p - 1 := Nat.dvd_of_mem_divisors hd
  have hN : p - 1 ≠ 0 := (sub_one_pos (p := p)).ne'
  have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors hd)
  have hq : (p - 1) / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdN)
    (Nat.pos_of_ne_zero hd0)).ne'
  have hω : IsPrimitiveRoot (S.ζ ^ ((p - 1) / d)) d := by
    have h := S.hζ.pow_of_dvd hq (Nat.div_dvd_of_dvd hdN)
    rwa [Nat.div_div_self hdN hN] at h
  have hterm : ∀ m, S.ζ ^ (k * (m * ((p - 1) / d))) = ((S.ζ ^ ((p - 1) / d)) ^ k) ^ m := by
    intro m
    rw [← pow_mul, ← pow_mul]
    ring_nf
  simp only [hterm]
  split_ifs with hk
  · rw [(hω.pow_eq_one_iff_dvd k).mpr hk]
    simp
  · have hne : (S.ζ ^ ((p - 1) / d)) ^ k ≠ 1 := fun h => hk ((hω.pow_eq_one_iff_dvd k).mp h)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- Divisors of `N` dividing `k` are the divisors of `gcd N k`. -/
theorem divisors_filter_dvd {N k : ℕ} (hN : N ≠ 0) :
    N.divisors.filter (· ∣ k) = (Nat.gcd N k).divisors := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left k (Nat.pos_of_ne_zero hN)).ne'⟩
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h1, hN⟩, h2⟩

/-- **The character identity for primitive roots.** -/
theorem generator_indicator (S : Setup p) (n : ℕ) :
    (if orderOf (n : ZMod p) = p - 1 then (1 : ℂ) else 0) =
      ∑ d ∈ (p - 1).divisors, ((μ d : ℂ) / d) *
        ∑ m ∈ range d, (S.χ ^ (m * ((p - 1) / d))) (n : ZMod p) := by
  have hN : p - 1 ≠ 0 := (sub_one_pos (p := p)).ne'
  by_cases hu : IsUnit (n : ZMod p)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, S.g ^ k = hu.unit := by
      have h := S.hg hu.unit
      rw [← mem_powers_iff_mem_zpowers] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k, hk⟩
    have hn : (n : ZMod p) = ((S.g ^ k : (ZMod p)ˣ) : ZMod p) := by rw [hk]; simp
    have hord : orderOf (n : ZMod p) = (p - 1) / Nat.gcd (p - 1) k := by
      rw [hn, orderOf_units, orderOf_pow,
        orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have hlhs : (if orderOf (n : ZMod p) = p - 1 then (1 : ℂ) else 0) =
        if Nat.gcd (p - 1) k = 1 then 1 else 0 := by
      rw [hord]
      congr 1
      apply propext
      rw [Nat.div_eq_self]
      simp [hN]
    rw [hlhs, ← sum_moebius_divisors, ← divisors_filter_dvd hN, sum_filter]
    refine sum_congr rfl (fun d hd => ?_)
    rw [hn]
    simp only [pow_apply_gen_pow]
    rw [sum_range_pow_root S hd k]
    have hd0 : (d : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    split_ifs
    · field_simp
    · simp
  · have hlhs : orderOf (n : ZMod p) ≠ p - 1 := by
      intro h
      apply hu
      apply IsUnit.of_pow_eq_one (n := p - 1) _ hN
      rw [← h]
      exact pow_orderOf_eq_one _
    simp only [hlhs, ↓reduceIte]
    symm
    apply sum_eq_zero
    intro d _
    simp [MulChar.map_nonunit _ hu]

/-- The terms with `0 < m < d` are nonprincipal. -/
theorem pow_ne_one (S : Setup p) {d m : ℕ} (hd : d ∈ (p - 1).divisors) (hm0 : 0 < m)
    (hmd : m < d) : S.χ ^ (m * ((p - 1) / d)) ≠ 1 := by
  have hdN : d ∣ p - 1 := Nat.dvd_of_mem_divisors hd
  have hN : p - 1 ≠ 0 := (sub_one_pos (p := p)).ne'
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hq : 0 < (p - 1) / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdN) hd0
  intro h
  have h1 := congrArg (fun χ : DirichletCharacter ℂ p => χ ((S.g ^ 1 : (ZMod p)ˣ) : ZMod p)) h
  simp only [pow_apply_gen_pow, MulChar.one_apply_coe, one_mul] at h1
  refine S.hζ.pow_ne_one_of_pos_of_lt (Nat.mul_pos hm0 hq).ne' ?_ h1
  calc m * ((p - 1) / d) < d * ((p - 1) / d) := Nat.mul_lt_mul_of_pos_right hmd hq
    _ = p - 1 := Nat.mul_div_cancel' hdN

/-- The Riesz-weighted prime sum over primitive roots. -/
noncomputable def genSum (p : ℕ) [Fact p.Prime] (x : ℝ) : ℂ :=
  Riesz.rieszSum
    (fun n => (if orderOf (n : ZMod p) = p - 1 then (1 : ℂ) else 0) * (Λ n : ℂ)) x

theorem genSum_eq (S : Setup p) (x : ℝ) :
    genSum p x = ∑ d ∈ (p - 1).divisors, ((μ d : ℂ) / d) *
      ∑ m ∈ range d, Riesz.rieszSum (↗(S.χ ^ (m * ((p - 1) / d))) * ↗Λ) x := by
  unfold genSum Riesz.rieszSum
  simp only [generator_indicator S, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun d _ => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun m _ => ?_)
  refine sum_congr rfl (fun n _ => ?_)
  simp only [Pi.mul_apply]
  ring

end Vinogradov.Characters
