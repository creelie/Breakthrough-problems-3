import Vinogradov.Mobius.Reciprocal

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set
open scoped Topology

theorem negative_real_part_bound_general
    {g : ℂ → ℂ} {c z : ℂ} {r R U A : ℝ} {N : ℕ}
    (hr : 0 < r) (hrR : r < R) (hU : 0 ≤ U) (hA : 0 ≤ A)
    (hN : 2 * r / (R - r) ≤ N)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hupper : ∀ w ∈ ball c R, (g w).re ≤ U)
    (hstrict : (g c).re < U) (hcentre : -(g c).re ≤ A)
    (hz : z ∈ closedBall c r) :
    -(g z).re ≤ (N : ℝ) * U + ((N : ℝ) + 1) * A := by
  have hM : 0 < U - (g c).re := sub_pos.mpr hstrict
  have hb := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
    (g := fun w => g w - g c) hr.le hrR hM (by norm_num : (0 : ℝ) ≤ 0)
    (hg.sub_const (g c))
    (fun w hw => by simpa only [Complex.sub_re] using sub_le_sub_right (hupper w hw) _)
    (by simp) hz
  have hb' : ‖g z - g c‖ ≤ (2 * r / (R - r)) * (U - (g c).re) := by
    convert hb using 1; ring
  have hRatioNonneg : 0 ≤ 2 * r / (R - r) := by positivity
  have hreal := (neg_le_abs (g z - g c).re).trans (Complex.abs_re_le_norm (g z - g c))
  simp only [Complex.sub_re] at hreal
  calc
    -(g z).re ≤ ‖g z - g c‖ - (g c).re := by linarith
    _ ≤ (2 * r / (R - r)) * (U - (g c).re) - (g c).re := sub_le_sub_right hb' _
    _ = (2 * r / (R - r)) * U + (2 * r / (R - r) + 1) * (-(g c).re) := by ring
    _ ≤ (2 * r / (R - r)) * U + (2 * r / (R - r) + 1) * A := by gcongr
    _ ≤ (N : ℝ) * U + ((N : ℝ) + 1) * A := by gcongr

/-- Polynomial reciprocal growth on every smaller closed strip of an arbitrary
zero-free half-plane. The exponent and constant are independent of q and chi. -/
theorem polynomial_reciprocal_of_nonvanishing
    {θ a : ℝ} (hθ : 0 < θ) (hθa : θ < a) (ha : a < 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        (∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0) →
        ∀ u t : ℝ, a ≤ u → u ≤ 2 →
          ‖(χ.LFunction ((u : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
            C * (q : ℝ) ^ N * (1 + |t|) ^ N := by
  let v : ℝ := (θ + a) / 2
  let r : ℝ := 2 - a
  let R : ℝ := 2 - v
  have hv : 0 < v := by dsimp [v]; linarith
  have hθv : θ < v := by dsimp [v]; linarith
  have hra : 0 < r := by dsimp [r]; linarith
  have hrr : r < R := by dsimp [r, R, v]; linarith
  have hR : 0 < R := hra.trans hrr
  let N : ℕ := ⌈2 * r / (R - r)⌉₊
  have hN : 2 * r / (R - r) ≤ N := Nat.le_ceil _
  have hNp : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity : 0 < 2 * r / (R - r)) hN
    exact_mod_cast this
  let D : ℝ := 2 + 4 / v
  have hD : 0 < D := by dsimp [D]; positivity
  let C : ℝ := Real.exp (((N : ℝ) + 1) * EulerLog.eulerLogBound) * D ^ N
  refine ⟨N, hNp, C, by dsimp [C]; positivity, ?_⟩
  intro q _ χ hχ hzero u t hua hu2
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqp : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  let c : ℂ := 2 + (t : ℂ) * I
  let B : ℝ := 2 + (q : ℝ) * (|t| + 4) / v
  have hB : 1 < B := by
    have hn : 0 ≤ (q : ℝ) * (|t| + 4) / v := by positivity
    dsimp [B]
    linarith
  have hBp : 0 < B := zero_lt_one.trans hB
  have hre (z : ℂ) (hz : z ∈ ball c R) : v < z.re := by
    have hn : ‖z - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hz
    have hrn := (neg_le_abs (z - c).re).trans (Complex.abs_re_le_norm (z - c))
    simp only [Complex.sub_re] at hrn
    have hc : c.re = 2 := by simp [c]
    rw [hc] at hrn
    dsimp [R] at hn
    linarith
  have hnorm (z : ℂ) (hz : z ∈ ball c R) : ‖z‖ ≤ |t| + 4 := by
    have hn : ‖z - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hz
    have hc : ‖c‖ ≤ 2 + |t| := by
      calc
        ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = 2 + |t| := by simp
    have hh := norm_le_norm_sub_add z c
    dsimp [R] at hn
    linarith
  have hgrowth (z : ℂ) (hz : z ∈ ball c R) : ‖χ.LFunction z‖ < B := by
    have hzv := hre z hz
    have hzn := hnorm z hz
    have hab := MRT.mrt_character_LFunction_norm_le χ hχ (hv.trans hzv)
    have hratio : (q : ℝ) * ‖z‖ / z.re ≤ (q : ℝ) * (|t| + 4) / v := by
      exact (div_le_div_of_nonneg_left (by positivity) hv hzv.le).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzn hqp.le) hv.le)
    exact (hab.trans hratio).trans_lt (by dsimp [B]; linarith)
  obtain ⟨g, hg, he, hgc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized
      (c := c) (R := R) (m := EulerLog.eulerLog χ c) hR
      (χ.differentiable_LFunction hχ).differentiableOn
      (fun z hz => hzero z (hθv.trans (hre z hz)))
      (EulerLog.exp_eulerLog χ (by simp [c]))
  have hupper (z : ℂ) (hz : z ∈ ball c R) : (g z).re < Real.log B := by
    have hh := hgrowth z hz
    have hez : Complex.exp (g z) = χ.LFunction z := he hz
    rw [← hez, Complex.norm_exp, ← Real.exp_log hBp] at hh
    exact Real.exp_lt_exp.mp hh
  have hcentre : -(g c).re ≤ EulerLog.eulerLogBound := by
    rw [hgc]
    exact ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
      (EulerLog.eulerLog_norm_le χ (by norm_num [c]))
  let z : ℂ := (u : ℂ) + (t : ℂ) * I
  have hz : z ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    have heq : z - c = ((u - 2 : ℝ) : ℂ) := by dsimp [z, c]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    dsimp [r]
    linarith
  have hneg := negative_real_part_bound_general hra hrr (Real.log_nonneg hB.le)
    (zero_le_one.trans EulerLog.eulerLogBound_ge_one) hN hg
    (fun w hw => (hupper w hw).le) (hupper c (mem_ball_self hR)) hcentre hz
  have hez : Complex.exp (g z) = χ.LFunction z := he (closedBall_subset_ball hrr hz)
  have hscale : B ≤ D * q * (1 + |t|) := by
    dsimp [B, D]
    have hqt : 0 ≤ (q : ℝ) * |t| := mul_nonneg hqp.le (abs_nonneg t)
    apply le_of_mul_le_mul_right (a := v) ?_ hv
    have hleft : (2 + (q : ℝ) * (|t| + 4) / v) * v =
        2 * v + (q : ℝ) * (|t| + 4) := by field_simp
    have hright : ((2 + 4 / v) * (q : ℝ) * (1 + |t|)) * v =
        (2 * v + 4) * (q : ℝ) * (1 + |t|) := by field_simp
    rw [hleft, hright]
    nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) - 1 by linarith) hv.le,
      mul_nonneg hqt (show 0 ≤ 2 * v + 3 by linarith)]
  change ‖(χ.LFunction z)⁻¹‖ ≤ _
  rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
  calc
    _ ≤ Real.exp ((N : ℝ) * Real.log B + ((N : ℝ) + 1) * EulerLog.eulerLogBound) :=
      Real.exp_le_exp.mpr hneg
    _ = Real.exp (((N : ℝ) + 1) * EulerLog.eulerLogBound) * B ^ N := by
      rw [add_comm, Real.exp_add, Real.exp_nat_mul, Real.exp_log hBp]
    _ ≤ Real.exp (((N : ℝ) + 1) * EulerLog.eulerLogBound) * (D * q * (1 + |t|)) ^ N := by
      gcongr
    _ = C * (q : ℝ) ^ N * (1 + |t|) ^ N := by dsimp [C]; simp only [mul_pow]; ring

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.polynomial_reciprocal_of_nonvanishing
