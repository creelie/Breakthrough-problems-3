import Vinogradov.Mobius.Bounds

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set MeasureTheory Filter Asymptotics
open scoped Topology Classical

theorem shifted_forward_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hzero : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {X : ℝ} (hX : 1 ≤ X) :
    (∫ t : ℝ, forwardKernel χ W X (((11 / 12 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, forwardKernel χ W X ((2 : ℂ) + (t : ℂ) * I) := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hScale := conductorScale_nonneg q
  obtain ⟨C, hC, hM⟩ := mellin_uniform_strip_bound hW (11 / 12) 2
  apply ContourShift.integral_eq_of_exponential_strip_growth
    (forwardKernel χ W X) (11 / 12) 2 104 (X ^ (2 : ℝ) * conductorScale q * C)
    (by norm_num) (by norm_num) (by positivity)
  · intro z hza hzb
    exact forwardKernel_differentiableAt χ hχ hzero hW X (by linarith)
  · exact forwardKernel_line_integrable χ hχ hzero hW hXp le_rfl (by norm_num)
  · exact forwardKernel_line_integrable χ hχ hzero hW hXp (by norm_num) le_rfl
  · intro u hu t
    have hMu : ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖ ≤ C :=
      hM _ (by simpa using hu.1) (by simpa using hu.2)
    have hpower : (1 + |t|) ^ (104 : ℕ) ≤ Real.exp (104 * |t|) := by
      calc
        (1 + |t|) ^ (104 : ℕ) ≤ (Real.exp |t|) ^ (104 : ℕ) := by
          gcongr
          linarith [Real.add_one_le_exp |t|]
        _ = Real.exp (104 * |t|) := (Real.exp_nat_mul |t| 104).symm
    calc
      _ ≤ X ^ u * conductorScale q *
          ((1 + |t|) ^ (104 : ℕ) * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖) :=
        forwardKernel_norm_le χ hχ hzero W hXp hu.1 hu.2
      _ ≤ X ^ (2 : ℝ) * conductorScale q * ((1 + |t|) ^ (104 : ℕ) * C) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hX hu.2) hScale
        · exact mul_le_mul_of_nonneg_left hMu (by positivity)
        · positivity
        · positivity
      _ = (X ^ (2 : ℝ) * conductorScale q * C) * (1 + |t|) ^ (104 : ℕ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

/-- The forward estimate for the actual smoothed twisted Mobius sum. Its
zero-free input is visible and is not obtained from the conclusion itself. -/
theorem smoothed_mobius_bound_of_seven_eighths {W : ℝ → ℂ} (hW : IsTestWeight W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 →
      (∀ s : ℂ, (7 / 8 : ℝ) < s.re → χ.LFunction s ≠ 0) →
      ∀ X : ℝ, 1 ≤ X →
        ‖smoothedSum χ W X‖ ≤ C * (q : ℝ) ^ (104 : ℕ) * X ^ (11 / 12 : ℝ) := by
  let mass : ℝ := ∫ t : ℝ, (1 + |t|) ^ (104 : ℕ) *
    ‖mellin W (((11 / 12 : ℝ) : ℂ) + (t : ℂ) * I)‖
  have hmass : 0 ≤ mass := integral_nonneg (fun t => by positivity)
  let C : ℝ := (1 / (2 * Real.pi)) * Real.exp (105 * EulerLog.eulerLogBound) *
    (7 : ℝ) ^ (104 : ℕ) * mass
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q _ χ hχ hzero X hX
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hinv := smoothedSum_eq_forward_integral χ hχ hzero hW hXp
  have hshift := shifted_forward_integral χ hχ hzero hW hX
  rw [← hshift] at hinv
  have hi : ‖∫ t : ℝ, forwardKernel χ W X (((11 / 12 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      X ^ (11 / 12 : ℝ) * conductorScale q * mass := by
    have hw := (mellin_polynomial_weight_integrable (11 / 12) hW 104).const_mul
      (X ^ (11 / 12 : ℝ) * conductorScale q)
    have hb := norm_integral_le_of_norm_le hw
      (Filter.Eventually.of_forall (fun t =>
        forwardKernel_norm_le χ hχ hzero W hXp (u := 11 / 12) (t := t) le_rfl (by norm_num)))
    simpa only [integral_const_mul, mass] using hb
  rw [hinv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (X ^ (11 / 12 : ℝ) * conductorScale q * mass) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = C * (q : ℝ) ^ (104 : ℕ) * X ^ (11 / 12 : ℝ) := by
      dsimp [C, conductorScale]
      rw [mul_pow]
      ring

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.shifted_forward_integral
#print axioms Vinogradov.Mobius.smoothed_mobius_bound_of_seven_eighths
