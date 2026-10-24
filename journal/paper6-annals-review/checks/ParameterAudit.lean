import Mathlib.Tactic.NormNum

namespace Paper6

theorem transfer_margins :
    (49 / 50 : ℚ) - (1 + (11 / 12 + 3 / 1000) - 47 / 50) = 1 / 3000 ∧
    (1800 : ℚ) / 50 - 34 = 2 ∧
    (25 : ℚ) * (1 - (11 / 12 + 3 / 1000)) - 2 = 1 / 120 := by
  norm_num

theorem old_cutoffs_insufficient :
    (700 : ℚ) / 50 < 34 ∧
    (17 : ℚ) * (1 - (11 / 12 + 3 / 1000)) < 2 := by
  norm_num

theorem progression_constants :
    (96 * 49 : ℚ) / 48 * (3 / 2) < 150 ∧
    (24 : ℚ) * (81 / 56) + 1 < 36 ∧
    (72 : ℚ) * (7 / 10) < 51 ∧
    (150 : ℚ) + 441 ≤ 600 ∧
    (600 : ℚ) * (56 * 11 + 1) = 370200 := by
  norm_num

end Paper6

#print axioms Paper6.transfer_margins
#print axioms Paper6.old_cutoffs_insufficient
#print axioms Paper6.progression_constants
