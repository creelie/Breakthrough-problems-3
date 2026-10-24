import Vinogradov.Analytic

/-!
# Reciprocal growth for the smoothed Mobius appendix

The zero-free input is an explicit hypothesis in this file. These theorems do
not prove it. The logarithm construction and Borel-Caratheodory helper used
below are credited OpenAI results in `LogarithmicControl`; the character Abel
bound is credited in `Vinogradov.MRT`. No test or extra axiom replaces them.
-/

namespace Vinogradov.Mobius

open Complex Metric Set
open scoped Topology

/-- The Harnack bound needed for radii 53/48 and 52/48, obtained by applying
Borel-Caratheodory to a logarithm with its centre value subtracted. -/
theorem negative_real_part_bound
    {g : ℂ → ℂ} {c z : ℂ} {U A : ℝ}
    (hg : DifferentiableOn ℂ g (ball c (53 / 48)))
    (hupper : ∀ w ∈ ball c (53 / 48), (g w).re ≤ U)
    (hstrict : (g c).re < U)
    (hcentre : -(g c).re ≤ A)
    (hz : z ∈ closedBall c (52 / 48)) :
    -(g z).re ≤ 104 * U + 105 * A := by
  have hM : 0 < U - (g c).re := sub_pos.mpr hstrict
  have hb := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
    (g := fun w => g w - g c) (c := c) (r := 52 / 48) (R := 53 / 48)
    (M := U - (g c).re) (A := 0)
    (by norm_num) (by norm_num) hM (by norm_num)
    (hg.sub_const (g c))
    (fun w hw => by simpa only [Complex.sub_re] using sub_le_sub_right (hupper w hw) _)
    (by simp) hz
  have hreal : -(g z - g c).re ≤ ‖g z - g c‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re] at hreal
  norm_num at hb
  nlinarith

/-- A concrete polynomial reciprocal bound. The constant is expressed through
the existing absolute Euler-logarithm bound; the conductor power is 104. -/
theorem reciprocal_bound_of_nonvanishing
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    {u t : ℝ} (hu : (11 / 12 : ℝ) ≤ u) (hu2 : u ≤ 2) :
    ‖(χ.LFunction ((u : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
      Real.exp (105 * EulerLog.eulerLogBound) * (7 * q * (1 + |t|)) ^ (104 : ℕ) := by
  let c : ℂ := 2 + (t : ℂ) * I
  let B : ℝ := 7 * q * (1 + |t|)
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hB : 0 < B := by dsimp [B]; positivity
  have hre (z : ℂ) (hz : z ∈ ball c (53 / 48)) : (43 / 48 : ℝ) < z.re := by
    have hn : ‖z - c‖ < (53 / 48 : ℝ) := by
      simpa only [mem_ball, dist_eq_norm] using hz
    have hr := (neg_le_abs (z - c).re).trans (Complex.abs_re_le_norm (z - c))
    simp only [Complex.sub_re] at hr
    have hc : c.re = 2 := by simp [c]
    rw [hc] at hr
    linarith
  have hgrowth (z : ℂ) (hz : z ∈ ball c (53 / 48)) : ‖χ.LFunction z‖ < B := by
    have hzr := hre z hz
    have hzn := Analytic.norm_le_of_mem_ball (r := 53 / 48) (by norm_num) hz
    have hab := MRT.mrt_character_LFunction_norm_le χ hχ (by linarith : 0 < z.re)
    have hratio : (q : ℝ) * ‖z‖ / z.re ≤ (q : ℝ) * (4 + |t|) / (43 / 48) := by
      exact (div_le_div_of_nonneg_left (mul_nonneg hq.le (norm_nonneg z))
        (by norm_num) hzr.le).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hq.le) (by norm_num))
    apply lt_of_le_of_lt (hab.trans hratio)
    dsimp [B]
    nlinarith [abs_nonneg t]
  obtain ⟨g, hg, he, hgc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized
      (c := c) (R := 53 / 48) (m := EulerLog.eulerLog χ c) (by norm_num)
      (χ.differentiable_LFunction hχ).differentiableOn
      (fun z hz => hzero z (by linarith [hre z hz]))
      (EulerLog.exp_eulerLog χ (by simp [c]))
  have hupper (z : ℂ) (hz : z ∈ ball c (53 / 48)) : (g z).re < Real.log B := by
    have hh := hgrowth z hz
    have hez : Complex.exp (g z) = χ.LFunction z := he hz
    rw [← hez, Complex.norm_exp, ← Real.exp_log hB] at hh
    exact Real.exp_lt_exp.mp hh
  have hcball : c ∈ ball c (53 / 48 : ℝ) := mem_ball_self (by norm_num)
  have hcentre : -(g c).re ≤ EulerLog.eulerLogBound := by
    rw [hgc]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
      (EulerLog.eulerLog_norm_le χ (by norm_num [c]))
  let z : ℂ := (u : ℂ) + (t : ℂ) * I
  have hz : z ∈ closedBall c (52 / 48 : ℝ) := by
    simp only [mem_closedBall, dist_eq_norm]
    have heq : z - c = ((u - 2 : ℝ) : ℂ) := by dsimp [z, c]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hneg := negative_real_part_bound hg (fun w hw => (hupper w hw).le)
    (hupper c hcball) hcentre hz
  have hez : Complex.exp (g z) = χ.LFunction z :=
    he (closedBall_subset_ball (by norm_num : (52 / 48 : ℝ) < 53 / 48) hz)
  change ‖(χ.LFunction z)⁻¹‖ ≤ _
  rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
  apply (Real.exp_le_exp.mpr hneg).trans_eq
  rw [show 104 * Real.log B + 105 * EulerLog.eulerLogBound =
      105 * EulerLog.eulerLogBound + (104 : ℕ) * Real.log B by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hB]

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.negative_real_part_bound
#print axioms Vinogradov.Mobius.reciprocal_bound_of_nonvanishing
