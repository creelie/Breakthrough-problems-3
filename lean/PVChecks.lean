/-!
Finite arithmetic used in the proofs of "Character sums with log log q outside a sparse set of
characters". Core Lean 4 only; every statement is checked by the kernel.
-/

/-- Section 5: R^{2/7} ≤ (2L)^5 because 16·2/7 < 5. -/
theorem exponent_twist : 16 * 2 < 5 * 7 := by decide

/-- Section 5: R^2 · R^{2/7} ≤ (2L)^{32+5} and the total power of log q is 37 + 14 = 51. -/
theorem exponent_total : 16 * 2 + 5 = 37 ∧ 37 + 14 = 51 := by decide

/-- Section 5: c_2 = 2^37 · 3^14 · c_9; the numerical factor. -/
theorem c2_factor : 2 ^ 37 * 3 ^ 14 = 657366253849018368 := by decide

/-- Section 5: with θ = a/b, the inequality 2(1-θ)/θ ≤ (16/7)(1-θ) holds when θ ≥ 7/8,
    i.e. 14 b ≤ 16 a whenever 7 b ≤ 8 a. -/
theorem theta_ratio (a b : Nat) (h : 7 * b ≤ 8 * a) : 14 * b ≤ 16 * a := by omega

/-- Section 5: θ = 1 - ε/8 with 0 < ε ≤ 1 gives θ ≥ 7/8 (scaled by 8: 8 - e ≥ 7 for e ≤ 1). -/
theorem theta_lower (e : Nat) (h : e ≤ 1) : 7 ≤ 8 - e := by omega

/-- Section 4: 3 + 2πR ≤ 8R for R ≥ 2, using π < 22/7 (scaled by 7). -/
theorem major_arc_factor (R : Nat) (h : 2 ≤ R) : 7 * 3 + 44 * R ≤ 7 * 8 * R := by omega

/-- Section 4: the product of the three bounds 8 · 9 = 72 (log² (qRt) ≤ 9 M²). -/
theorem major_arc_const : 8 * 9 = 72 ∧ 16 + 16 + 2 + 6 = 40 := by decide

/-- Section 4: A ≤ 40/(1-θ) + 1 ≤ 41/(1-θ) and log M ≤ log 2L ≤ 2 log L, so log Y ≤ 82/(1-θ) log L;
    the final constant is 2 · 82 = 164. -/
theorem harm_const : 41 * 2 = 82 ∧ 2 * 82 = 164 := by decide

/-- Section 4: 2L ≤ L² for L ≥ 2, which gives log(2L) ≤ 2 log L. -/
theorem two_L_le_sq (L : Nat) (h : 2 ≤ L) : 2 * L ≤ L * L := Nat.mul_le_mul_right L h

/-- Section 6: θ = 1 - ε/5 gives c_5 = 20 c_16 from (1-θ)^{-1} = 5/ε and the factor 4. -/
theorem logder_const : 5 * 4 = 20 := by decide

/-- Section 7: the character count 5,733,937 is the sum of the ten ranges of Table 2. -/
theorem character_total :
    75790 + 200653 + 316519 + 419444 + 534391 + 626370 + 760503 + 802881 + 935004 + 1062382
      = 5733937 := by decide

/-- Section 7: the counts above one half and three quarters of √q log log q. -/
theorem tail_totals :
    10176 + 18986 + 25260 + 30252 + 35798 + 39142 + 45298 + 45607 + 51348 + 56327 = 358194 ∧
    326 + 201 + 203 + 190 + 172 + 218 + 212 + 195 + 185 + 229 = 2131 := by decide

/-- Section 7: the number of moduli. -/
theorem moduli_total : 166 + 135 + 127 + 120 + 119 + 114 + 117 + 107 + 110 + 112 = 1227 := by decide
