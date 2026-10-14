import Mathlib

/-!
# A holomorphic logarithm of a Dirichlet L-function on `re s > 1`

For a Dirichlet character `χ`, the Euler logarithm
`E(s) = ∑_p -log (1 - χ(p) p^{-s})` is holomorphic on `re s > 1`, satisfies
`exp (E s) = L(s, χ)` there, and is bounded on `re s ≥ 3/2` by a constant that does
not depend on `χ` or on its modulus.

The structure follows `OAI/NumberTheory/DirichletL/Hecke/EulerLog.lean` of OpenAI's
`math` repository (Apache License 2.0), specialised from Hecke characters to Dirichlet
characters.
-/

namespace Vinogradov.EulerLog

open Complex Set Metric Filter
open scoped Topology

variable {q : ℕ}

/-- The `p`-th term `χ(p) p^{-s}` of the Euler product. -/
noncomputable def term (χ : DirichletCharacter ℂ q) (s : ℂ) (p : Nat.Primes) : ℂ :=
  χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s)

/-- The Euler logarithm of `L(s, χ)`. -/
noncomputable def eulerLog (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - term χ s p)

/-- A summable majorant of the logarithms of the Euler factors on `re s ≥ σ`. -/
noncomputable def majorant (σ : ℝ) (p : Nat.Primes) : ℝ :=
  (3 / 2) * ((p : ℕ) : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  exact (Nat.Primes.summable_rpow.mpr (by linarith : -σ < -1)).mul_left (3 / 2)

theorem term_norm_le (χ : DirichletCharacter ℂ q) (p : Nat.Primes) {s : ℂ} {σ : ℝ}
    (hs : σ ≤ s.re) : ‖term χ s p‖ ≤ ((p : ℕ) : ℝ) ^ (-σ) := by
  have hp : 0 < (p : ℕ) := p.prop.pos
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  rw [term, norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
    (Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hs))

theorem term_norm_le_half (χ : DirichletCharacter ℂ q) (p : Nat.Primes) {s : ℂ}
    (hs : 1 ≤ s.re) : ‖term χ s p‖ ≤ 1 / 2 := by
  refine (term_norm_le χ p hs).trans ?_
  rw [Real.rpow_neg_one]
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  rw [one_div]
  exact inv_anti₀ (by norm_num) h2

theorem log_factor_norm_le (χ : DirichletCharacter ℂ q) (p : Nat.Primes) {s : ℂ} {σ : ℝ}
    (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - term χ s p)‖ ≤ majorant σ p := by
  have hhalf := term_norm_le_half χ p (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self (z := -term χ s p) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (term_norm_le χ p hs) (by norm_num))

theorem term_differentiable (χ : DirichletCharacter ℂ q) (p : Nat.Primes) :
    Differentiable ℂ (fun s ↦ term χ s p) := by
  have hn : (((p : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (χ : DirichletCharacter ℂ q) (p : Nat.Primes) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - term χ s p)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn : ‖term χ s p‖ < 1 :=
    (term_norm_le_half χ p hs.le).trans_lt (by norm_num)
  have hslit : 1 - term χ s p ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -term χ s p) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (term_differentiable χ p s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog χ) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro p
    exact (log_factor_differentiableOn χ p).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact log_factor_norm_le χ p hσ.le hs.le

theorem eulerLog_differentiableOn (χ : DirichletCharacter ℂ q) :
    DifferentiableOn ℂ (eulerLog χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane χ hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (eulerLog χ s) = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← χ.LSeries_eulerProduct_exp_log hs]
  rfl

/-- A bound for the Euler logarithm on `re s ≥ 3/2`, uniform in the character. -/
noncomputable def eulerLogBound : ℝ := 1 + ∑' p : Nat.Primes, majorant (3 / 2) p

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' p : Nat.Primes, majorant (3 / 2) p :=
    tsum_nonneg (fun p ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖eulerLog χ s‖ ≤ eulerLogBound := by
  have hb : ∀ p : Nat.Primes, ‖-Complex.log (1 - term χ s p)‖ ≤ majorant (3 / 2) p :=
    fun p ↦ log_factor_norm_le χ p (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun p : Nat.Primes ↦ ‖-Complex.log (1 - term χ s p)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog χ s‖ ≤ ∑' p : Nat.Primes, ‖-Complex.log (1 - term χ s p)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes, majorant (3 / 2) p := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

/-- The three facts about the Euler logarithm used by the logarithmic control lemma. -/
theorem eulerLog_inner_disk [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog χ) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog χ) (DirichletCharacter.LFunction χ)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog χ s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn χ).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog χ (hsub hs)
  · intro s hs
    exact eulerLog_norm_le χ (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

end Vinogradov.EulerLog
