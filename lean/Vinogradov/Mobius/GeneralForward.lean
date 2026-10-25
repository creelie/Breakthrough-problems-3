import Vinogradov.Mobius.GeneralReciprocal
import Vinogradov.Mobius.Forward

noncomputable section
namespace Vinogradov.Mobius

open Complex Metric Set MeasureTheory Filter Asymptotics
open scoped Topology Classical

theorem kernel_differentiableAt_of_nonzero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {W : ℝ → ℂ} (hW : IsTestWeight W) (X : ℝ) (s : ℂ)
    (hL : χ.LFunction s ≠ 0) : DifferentiableAt ℂ (forwardKernel χ W X) s := by
  have hM : DifferentiableAt ℂ (mellin W) s := by
    have ha := CompactMellin.compact_weight_mellin_analytic W hW.1 hW.vanishes (s.re - 1)
    exact (ha s (by change s.re - 1 < s.re; linarith)).differentiableAt
  have hE : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((Real.log X : ℂ) * z)) s := by
    fun_prop
  exact (hE.mul hM).div (χ.differentiable_LFunction hχ s) hL

theorem kernel_norm_of_reciprocal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) {X u t D : ℝ} {N : ℕ}
    (hX : 0 < X)
    (hR : ‖(χ.LFunction ((u : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ D * (1 + |t|) ^ N) :
    ‖forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)‖ ≤
      X ^ u * D * ((1 + |t|) ^ N * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖) := by
  have he : ‖Complex.exp ((Real.log X : ℂ) * ((u : ℂ) + (t : ℂ) * I))‖ = X ^ u := by
    simp [Complex.norm_exp, Complex.mul_re, Real.rpow_def_of_pos hX]
  unfold forwardKernel
  rw [div_eq_mul_inv, norm_mul, norm_mul, he]
  calc
    _ ≤ X ^ u * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖ * (D * (1 + |t|) ^ N) := by gcongr
    _ = _ := by ring

theorem kernel_integrable_of_reciprocal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {X u D : ℝ} {N : ℕ} (hX : 0 < X)
    (hzero : ∀ t : ℝ, χ.LFunction ((u : ℂ) + (t : ℂ) * I) ≠ 0)
    (hR : ∀ t : ℝ, ‖(χ.LFunction ((u : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ D * (1 + |t|) ^ N) :
    Integrable (fun t : ℝ => forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)) := by
  have hc : Continuous (fun t : ℝ => forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun v : ℝ => (u : ℂ) + (v : ℂ) * I)
      (kernel_differentiableAt_of_nonzero χ hχ hW X _ (hzero t)).continuousAt
      (by fun_prop)
  apply ((mellin_polynomial_weight_integrable u hW N).const_mul (X ^ u * D)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => kernel_norm_of_reciprocal χ W hX (hR t))

theorem smoothed_bound_of_reciprocal_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ a D : ℝ} {N : ℕ} (hθa : θ < a) (ha : a ≤ 2) (hD : 0 ≤ D)
    (hzero : ∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0)
    (hR : ∀ u t : ℝ, a ≤ u → u ≤ 2 →
      ‖(χ.LFunction ((u : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ D * (1 + |t|) ^ N)
    {W : ℝ → ℂ} (hW : IsTestWeight W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 1 ≤ X → ‖smoothedSum χ W X‖ ≤ B * X ^ a := by
  let mass : ℝ := ∫ t : ℝ, (1 + |t|) ^ N * ‖mellin W ((a : ℂ) + (t : ℂ) * I)‖
  have hmass : 0 ≤ mass := integral_nonneg (fun t => by positivity)
  let B : ℝ := (1 / (2 * Real.pi)) * D * mass
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro X hX
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hint (u : ℝ) (hua : a ≤ u) (hu2 : u ≤ 2) :
      Integrable (fun t : ℝ => forwardKernel χ W X ((u : ℂ) + (t : ℂ) * I)) :=
    kernel_integrable_of_reciprocal χ hχ hW hXp
      (fun t => hzero _ (by simp; linarith)) (fun t => hR u t hua hu2)
  have hvertical : VerticalIntegrable (fun s => mellin W s / χ.LFunction s) 2 := by
    have hi := kernel_integrable_of_reciprocal χ hχ hW (X := 1) (u := 2) (by norm_num)
      (fun t => hzero _ (by simp; linarith)) (fun t => hR 2 t ha le_rfl)
    simpa only [forwardKernel, Real.log_one, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul, Complex.VerticalIntegrable] using hi
  have hinv := forward_mellin_inversion χ hW hXp hvertical
  obtain ⟨C, hC, hM⟩ := mellin_uniform_strip_bound hW a 2
  have hshift : (∫ t : ℝ, forwardKernel χ W X ((a : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, forwardKernel χ W X ((2 : ℂ) + (t : ℂ) * I) := by
    apply ContourShift.integral_eq_of_exponential_strip_growth
      (forwardKernel χ W X) a 2 N (X ^ (2 : ℝ) * D * C) ha (by positivity) (by positivity)
    · intro z hza hzb
      exact kernel_differentiableAt_of_nonzero χ hχ hW X z (hzero z (by linarith))
    · exact hint a le_rfl ha
    · exact hint 2 ha le_rfl
    · intro u hu t
      have hMu : ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖ ≤ C :=
        hM _ (by simpa using hu.1) (by simpa using hu.2)
      have hpower : (1 + |t|) ^ N ≤ Real.exp ((N : ℝ) * |t|) := by
        calc
          (1 + |t|) ^ N ≤ (Real.exp |t|) ^ N := by
            gcongr
            linarith [Real.add_one_le_exp |t|]
          _ = Real.exp ((N : ℝ) * |t|) := (Real.exp_nat_mul |t| N).symm
      calc
        _ ≤ X ^ u * D * ((1 + |t|) ^ N * ‖mellin W ((u : ℂ) + (t : ℂ) * I)‖) :=
          kernel_norm_of_reciprocal χ W hXp (hR u t hu.1 hu.2)
        _ ≤ X ^ (2 : ℝ) * D * ((1 + |t|) ^ N * C) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hX hu.2) hD
          · exact mul_le_mul_of_nonneg_left hMu (by positivity)
          · positivity
          · positivity
        _ = (X ^ (2 : ℝ) * D * C) * (1 + |t|) ^ N := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)
  rw [← hshift] at hinv
  have hi : ‖∫ t : ℝ, forwardKernel χ W X ((a : ℂ) + (t : ℂ) * I)‖ ≤ X ^ a * D * mass := by
    have hw := (mellin_polynomial_weight_integrable a hW N).const_mul (X ^ a * D)
    have hb := norm_integral_le_of_norm_le hw
      (Filter.Eventually.of_forall (fun t => kernel_norm_of_reciprocal χ W hXp (hR a t le_rfl ha)))
    simpa only [integral_const_mul, mass] using hb
  rw [hinv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (X ^ a * D * mass) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B * X ^ a := by dsimp [B]; ring

/-- The forward implication for every fixed boundary, with the global X>=1
quantifier used in the written appendix. -/
theorem smoothed_bounds_of_nonvanishing {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hzero : ∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0)
    {W : ℝ → ℂ} (hW : IsTestWeight W) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℝ, 1 ≤ X → ‖smoothedSum χ W X‖ ≤ B * X ^ (θ + ε) := by
  let d : ℝ := min (ε / 2) ((1 - θ) / 2)
  let a : ℝ := θ + d
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hθa : θ < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by
    have hh : d ≤ (1 - θ) / 2 := min_le_right _ _
    dsimp [a]
    linarith
  have haε : a ≤ θ + ε := by
    have hh : d ≤ ε / 2 := min_le_left _ _
    dsimp [a]
    linarith
  obtain ⟨N, hN, C, hC, hrec⟩ := polynomial_reciprocal_of_nonvanishing hθ hθa ha1
  have hD : 0 ≤ C * (q : ℝ) ^ N := by positivity
  obtain ⟨B, hB, hb⟩ := smoothed_bound_of_reciprocal_strip χ hχ hθa (by linarith : a ≤ 2) hD hzero
    (fun u t hua hu2 => hrec q χ hχ hzero u t hua hu2) hW
  refine ⟨B, hB, ?_⟩
  intro X hX
  exact (hb X hX).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX haε) hB)

theorem nonvanishing_iff_smoothed_bounds {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∀ s : ℂ, θ < s.re → χ.LFunction s ≠ 0) ↔
      ∀ ε : ℝ, 0 < ε → ∀ W : ℝ → ℂ, IsTestWeight W →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
          ‖smoothedSum χ W X‖ ≤ C * X ^ (θ + ε) := by
  constructor
  · intro hz ε hε W hW
    exact smoothed_bounds_of_nonvanishing χ hχ hθ hθ1 hz hW hε
  · intro hb s hs
    apply nonvanishing_of_smoothed_mobius_cancellation χ hχ hθ1 (fun ε hε W hW => ?_) hs
    obtain ⟨C, hC, hbound⟩ := hb ε hε W hW
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ X) _)]
      using hbound X hX

end Vinogradov.Mobius

#print axioms Vinogradov.Mobius.smoothed_bounds_of_nonvanishing
#print axioms Vinogradov.Mobius.nonvanishing_iff_smoothed_bounds
