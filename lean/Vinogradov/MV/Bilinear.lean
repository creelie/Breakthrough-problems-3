import Vinogradov.MV.Spacing

/-!
# Bilinear sums with a geometric inner sum

`∑_{U < u ≤ 2U} |∑_{v ∈ V, uv ≤ N} b(v) e(uvα)|² ≤ ∑_{v, v'} |b(v)| |b(v')| wt_U((v - v')α)`,
since the sum over `u` is geometric, and `∑_{m, m' ≤ H} wt((m - m')α) ≤ H (M + 2 ∑_{h ≤ H} wt(hα))`.
-/

namespace Vinogradov.MV

open Finset Complex Vinogradov.PV

theorem e_int (k : ℤ) : e k = 1 := by
  unfold e
  rw [show 2 * (Real.pi : ℂ) * I * ((k : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

theorem e_nat_mul_sub_round (x : ℕ) (θ : ℝ) : e (x * θ) = e (x * (θ - round θ)) := by
  have : (x : ℝ) * θ = x * (θ - round θ) + ((x * round θ : ℤ) : ℝ) := by push_cast; ring
  rw [this, e_add, e_int, mul_one]

/-- **Geometric sums.** `‖∑_{A < x ≤ B} e(xθ)‖ ≤ wt_P(θ)` when `B ≤ A + P`. -/
theorem norm_sum_Ioc_e_le (θ : ℝ) {P : ℝ} (hP : 0 < P) (A B : ℕ) (hAB : (B : ℝ) ≤ A + P) :
    ‖∑ x ∈ Ioc A B, e (x * θ)‖ ≤ wt P θ := by
  by_cases h : nint θ < 1 / P
  · rw [wt, if_pos h]
    calc ‖∑ x ∈ Ioc A B, e (x * θ)‖ ≤ ∑ x ∈ Ioc A B, ‖e (x * θ)‖ := norm_sum_le _ _
      _ = (#(Ioc A B) : ℝ) := by simp [norm_e]
      _ ≤ P := by
          rw [Nat.card_Ioc]
          rcases le_or_gt A B with hle | hlt
          · rw [Nat.cast_sub hle]; linarith
          · rw [Nat.sub_eq_zero_of_le hlt.le]; simp; linarith
  · push_neg at h
    rw [one_div_le_wt hP h]
    set δ := θ - round θ with hδdef
    have hδ : |δ| = nint θ := rfl
    have hδ0 : 0 < |δ| := lt_of_lt_of_le (by positivity) (hδ ▸ h)
    have hw := norm_one_sub_e_ge (hδ ▸ nint_le_half θ)
    have hwpos : 0 < ‖1 - e (-δ)‖ := by linarith
    have hw0 : 1 - e (-δ) ≠ 0 := norm_pos_iff.1 hwpos
    have hrw : ∀ x : ℕ, e (x * θ) = e (x * δ) := fun x => e_nat_mul_sub_round x θ
    simp_rw [hrw]
    rcases le_or_gt A B with hle | hlt
    · have hsplit := sum_Ioc_consecutive (fun x : ℕ => e (x * δ)) (Nat.zero_le A) hle
      have heq : ∑ x ∈ Ioc A B, e (x * δ) = (e (B * δ) - e (A * δ)) / (1 - e (-δ)) := by
        rw [eq_sub_of_add_eq' hsplit, sum_e_geom δ hw0, sum_e_geom δ hw0]
        field_simp; ring
      rw [heq, norm_div]
      have hnum : ‖e (B * δ) - e (A * δ)‖ ≤ 2 := by
        calc ‖e (B * δ) - e (A * δ)‖ ≤ ‖e (B * δ)‖ + ‖e (A * δ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_e, norm_e]; norm_num
      rw [div_le_div_iff₀ hwpos (by rw [← hδ]; exact hδ0)]
      rw [← hδ]; nlinarith
    · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]
      exact div_nonneg zero_le_one (nint_nonneg θ)

/-- `∑_u ‖∑_v a(u, v)‖² ≤ ∑_{v, v'} ‖∑_u a(u, v) conj a(u, v')‖`. -/
theorem sum_norm_sq_le (I V : Finset ℕ) (a : ℕ → ℕ → ℂ) :
    ∑ u ∈ I, ‖∑ v ∈ V, a u v‖ ^ 2 ≤
      ∑ v ∈ V, ∑ v' ∈ V, ‖∑ u ∈ I, a u v * (starRingEnd ℂ) (a u v')‖ := by
  have key : ∀ u, ‖∑ v ∈ V, a u v‖ ^ 2 =
      (∑ v ∈ V, ∑ v' ∈ V, a u v * (starRingEnd ℂ) (a u v')).re := by
    intro u
    rw [← sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  simp_rw [key]
  rw [← Complex.re_sum, sum_comm]
  refine le_trans (Complex.re_le_norm _) ?_
  refine le_trans (norm_sum_le _ _) (sum_le_sum fun v _ => ?_)
  rw [sum_comm]
  exact norm_sum_le _ _

theorem filter_Ioc_mul_le (A B N v v' : ℕ) (hv : 0 < v) (hv' : 0 < v') :
    (Ioc A B).filter (fun u => u * v ≤ N ∧ u * v' ≤ N) = Ioc A (min B (min (N / v) (N / v'))) := by
  ext u
  simp only [mem_filter, mem_Ioc, le_min_iff]
  rw [Nat.le_div_iff_mul_le hv, Nat.le_div_iff_mul_le hv']
  tauto

/-- **Bilinear sums.** For `B ≤ A + U`,
`∑_{A < u ≤ B} ‖∑_{v ∈ V, uv ≤ N} b(v) e(uvα)‖² ≤ ∑_{v, v' ∈ V} ‖b(v)‖ ‖b(v')‖ wt_U((v - v')α)`. -/
theorem bilinear_wt (A B N : ℕ) {U : ℝ} (hU : 0 < U) (hAB : (B : ℝ) ≤ A + U) (V : Finset ℕ)
    (hV : ∀ v ∈ V, 0 < v) (b : ℕ → ℂ) (α : ℝ) :
    ∑ u ∈ Ioc A B, ‖∑ v ∈ V, (if u * v ≤ N then b v * e (u * v * α) else 0)‖ ^ 2 ≤
      ∑ v ∈ V, ∑ v' ∈ V, ‖b v‖ * ‖b v'‖ * wt U (((v : ℝ) - v') * α) := by
  refine le_trans (sum_norm_sq_le _ _ _) (sum_le_sum fun v hv => sum_le_sum fun v' hv' => ?_)
  have hprod : ∀ u : ℕ, (if u * v ≤ N then b v * e (u * v * α) else 0) *
      (starRingEnd ℂ) (if u * v' ≤ N then b v' * e (u * v' * α) else 0) =
      if u * v ≤ N ∧ u * v' ≤ N then
        (b v * (starRingEnd ℂ) (b v')) * e (u * (((v : ℝ) - v') * α)) else 0 := by
    intro u
    by_cases h1 : u * v ≤ N <;> by_cases h2 : u * v' ≤ N <;> simp [h1, h2]
    rw [conj_e]
    have : (u : ℝ) * (((v : ℝ) - v') * α) = u * v * α + -(u * v' * α) := by ring
    rw [this, e_add]; ring
  simp_rw [hprod]
  rw [← sum_filter, ← mul_sum, filter_Ioc_mul_le A B N v v' (hV v hv) (hV v' hv'), norm_mul,
    norm_mul, Complex.norm_conj]
  gcongr
  apply norm_sum_Ioc_e_le _ hU
  have : min B (min (N / v) (N / v')) ≤ B := min_le_left _ _
  calc ((min B (min (N / v) (N / v')) : ℕ) : ℝ) ≤ B := by exact_mod_cast this
    _ ≤ A + U := hAB

/-- **Double sums.** -/
theorem double_sum_wt (H : ℕ) {M : ℝ} (hM : 0 < M) (α : ℝ) :
    ∑ m ∈ Ioc 0 H, ∑ m' ∈ Ioc 0 H, wt M (((m : ℝ) - m') * α) ≤
      H * (M + 2 * ∑ h ∈ Icc 1 H, wt M (h * α)) := by
  have hnn : ∀ θ, 0 ≤ wt M θ := wt_nonneg hM.le
  have hrow : ∀ m ∈ Ioc 0 H, ∑ m' ∈ Ioc 0 H, wt M (((m : ℝ) - m') * α) ≤
      M + 2 * ∑ h ∈ Icc 1 H, wt M (h * α) := by
    intro m hm
    rw [mem_Ioc] at hm
    rw [← sum_filter_add_sum_filter_not (Ioc 0 H) (fun m' => m' < m),
      ← sum_filter_add_sum_filter_not ((Ioc 0 H).filter fun m' => ¬ m' < m) (fun m' => m' = m)]
    -- `m' < m`
    have h1 : ∑ m' ∈ (Ioc 0 H).filter (fun m' => m' < m), wt M (((m : ℝ) - m') * α) ≤
        ∑ h ∈ Icc 1 H, wt M (h * α) := by
      have hinj : Set.InjOn (fun m' => m - m') ↑((Ioc 0 H).filter (fun m' => m' < m)) := by
        intro x hx y hy hxy
        simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hx hy
        simp only at hxy; omega
      calc ∑ m' ∈ (Ioc 0 H).filter (fun m' => m' < m), wt M (((m : ℝ) - m') * α)
          = ∑ m' ∈ (Ioc 0 H).filter (fun m' => m' < m), wt M (((m - m' : ℕ) : ℝ) * α) := by
            apply sum_congr rfl; intro m' hm'
            rw [mem_filter] at hm'
            rw [Nat.cast_sub hm'.2.le]
        _ = ∑ h ∈ ((Ioc 0 H).filter (fun m' => m' < m)).image (fun m' => m - m'),
              wt M (h * α) := (sum_image (f := fun h : ℕ => wt M ((h : ℝ) * α)) hinj).symm
        _ ≤ ∑ h ∈ Icc 1 H, wt M (h * α) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro h hh
              simp only [mem_image, mem_filter, mem_Ioc] at hh
              obtain ⟨m', hm', rfl⟩ := hh
              rw [mem_Icc]; omega
            · intro _ _ _; exact hnn _
    -- `m' > m`
    have h3 : ∑ m' ∈ ((Ioc 0 H).filter fun m' => ¬ m' < m).filter (fun m' => ¬ m' = m),
        wt M (((m : ℝ) - m') * α) ≤ ∑ h ∈ Icc 1 H, wt M (h * α) := by
      set S := ((Ioc 0 H).filter fun m' => ¬ m' < m).filter (fun m' => ¬ m' = m)
      have hS : ∀ m' ∈ S, m < m' ∧ m' ≤ H := by
        intro m' hm'; simp only [S, mem_filter, mem_Ioc] at hm'; omega
      have hinj : Set.InjOn (fun m' => m' - m) ↑S := by
        intro x hx y hy hxy
        have := hS x hx; have := hS y hy
        simp only at hxy; omega
      calc ∑ m' ∈ S, wt M (((m : ℝ) - m') * α)
          = ∑ m' ∈ S, wt M (((m' - m : ℕ) : ℝ) * α) := by
            apply sum_congr rfl; intro m' hm'
            rw [Nat.cast_sub (hS m' hm').1.le, ← wt_neg]; ring_nf
        _ = ∑ h ∈ S.image (fun m' => m' - m), wt M (h * α) := (sum_image (f := fun h : ℕ => wt M ((h : ℝ) * α)) hinj).symm
        _ ≤ ∑ h ∈ Icc 1 H, wt M (h * α) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro h hh
              simp only [mem_image] at hh
              obtain ⟨m', hm', rfl⟩ := hh
              have := hS m' hm'
              rw [mem_Icc]; omega
            · intro _ _ _; exact hnn _
    -- `m' = m`
    have h2 : ∑ m' ∈ ((Ioc 0 H).filter fun m' => ¬ m' < m).filter (fun m' => m' = m),
        wt M (((m : ℝ) - m') * α) ≤ M := by
      have hsub : ((Ioc 0 H).filter fun m' => ¬ m' < m).filter (fun m' => m' = m) ⊆ {m} := by
        intro x hx; simp only [mem_filter] at hx; simp [hx.2]
      calc _ ≤ ∑ m' ∈ ({m} : Finset ℕ), wt M (((m : ℝ) - m') * α) :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hnn _)
        _ ≤ M := by rw [sum_singleton]; exact wt_le hM _
    linarith
  calc ∑ m ∈ Ioc 0 H, ∑ m' ∈ Ioc 0 H, wt M (((m : ℝ) - m') * α)
      ≤ ∑ _m ∈ Ioc 0 H, (M + 2 * ∑ h ∈ Icc 1 H, wt M (h * α)) := sum_le_sum hrow
    _ = H * (M + 2 * ∑ h ∈ Icc 1 H, wt M (h * α)) := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp

end Vinogradov.MV
