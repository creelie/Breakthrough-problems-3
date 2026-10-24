import Vinogradov.Mobius.Forward

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set MeasureTheory Filter Asymptotics
open scoped Topology Classical

def conductorScale (q : ℕ) : ℝ :=
  Real.exp (105 * EulerLog.eulerLogBound) * (7 * q) ^ (104 : ℕ)

theorem conductorScale_nonneg (q : ℕ) : 0 ≤ conductorScale q := by
  unfold conductorScale
  positivity

theorem forwardKernel_differentiableAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    {W : ℝ → ℂ} (hW : IsTestWeight W) (X : ℝ)
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    DifferentiableAt ℂ (forwardKernel χ W X) s := by
  have hM : DifferentiableAt ℂ (mellin W) s := by
    have ha := CompactMellin.compact_weight_mellin_analytic W hW.1 hW.vanishes (s.re - 1)
    exact (ha s (by change s.re - 1 < s.re; linarith)).differentiableAt
  have hE : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((Real.log X : ℂ) * z)) s := by
    fun_prop
  exact (hE.mul hM).div (χ.differentiable_LFunction hχ s) (hzero s hs)

theorem forwardKernel_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    {u t : ℝ} (hu : (11 / 12 : ℝ) ≤ u) (hu2 : u ≤ 2) :
    ‖forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)‖ ≤
      X ^ u * conductorScale q *
        ((1 + |t|) ^ (104 : ℕ) * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖) := by
  have he : ‖Complex.exp ((Real.log X : ℂ) * ((u : ℂ) + (t : ℂ) * I))‖ = X ^ u := by
    simp [Complex.norm_exp, Complex.mul_re, Real.rpow_def_of_pos hX]
  have hr := reciprocal_bound_of_nonvanishing χ hχ hzero (t := t) hu hu2
  unfold forwardKernel
  rw [div_eq_mul_inv, norm_mul, norm_mul, he]
  calc
    _ ≤ X ^ u * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖ *
        (Real.exp (105 * EulerLog.eulerLogBound) * (7 * q * (1 + |t|)) ^ (104 : ℕ)) := by
          gcongr
    _ = _ := by simp only [conductorScale, mul_pow]; ring

theorem forwardKernel_line_integrable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {X : ℝ} (hX : 0 < X)
    {u : ℝ} (hu : (11 / 12 : ℝ) ≤ u) (hu2 : u ≤ 2) :
    Integrable (fun t : ℝ => forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)) := by
  have hc : Continuous (fun t : ℝ => forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (forwardKernel_differentiableAt χ hχ hzero hW X (by simp; linarith)).continuousAt.comp
      (by fun_prop)
  apply ((mellin_polynomial_weight_integrable u hW 104).const_mul
    (X ^ u * conductorScale q)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => forwardKernel_norm_le χ hχ hzero W hX hu hu2)

theorem smoothedSum_eq_forward_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {X : ℝ} (hX : 0 < X) :
    smoothedSum χ W X = (1 / (2 * Real.pi)) •
      ∫ t : ℝ, forwardKernel χ W X ((2 : ℂ) + (t : ℂ) * I) := by
  apply forward_mellin_inversion χ hW hX
  have hi := forwardKernel_line_integrable χ hχ hzero hW (X := 1) (by norm_num)
    (u := 2) (by norm_num) le_rfl
  simpa only [forwardKernel, Real.log_one, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul, Complex.VerticalIntegrable] using hi

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.forwardKernel_line_integrable
#print axioms Vinogradov.Mobius.smoothedSum_eq_forward_integral
