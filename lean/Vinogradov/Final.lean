import Vinogradov.Main
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# Prime primitive roots below `p^ε`

The zero-free half-plane `re s > 7/8` of OpenAI's formalization discharges the hypothesis
`ZeroFree` of `Vinogradov.Main`.
-/

namespace Vinogradov

/-- No `L(s, χ)` with `χ` nonprincipal vanishes on `re s > 7/8`. -/
theorem zeroFree : Main.ZeroFree := by
  intro q _ χ hχ z hz
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hz
    (fun h => hχ h.1)

/-- **Theorem 1.1.** For every `η > 0` there is `C` such that every prime `p` has a prime
primitive root `ℓ ≤ C (τ(p-1)² log (p + 2))^{8+η}`. -/
theorem least_prime_primitive_root_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (((p - 1).divisors.card : ℝ) ^ 2 * Real.log (p + 2)) ^ (8 + η) :=
  Main.least_prime_primitive_root_bound zeroFree hη

/-- **Theorem 1.2** (Vinogradov's conjecture, prime form). For every `ε > 0` there is `C` such
that every prime `p` has a prime primitive root `ℓ ≤ C p^ε`. -/
theorem least_prime_primitive_root_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → ∃ ℓ : ℕ, ℓ.Prime ∧ orderOf (ℓ : ZMod p) = p - 1 ∧
      (ℓ : ℝ) ≤ C * (p : ℝ) ^ ε :=
  Main.least_prime_primitive_root_le_rpow zeroFree hε

/-- **Theorem 1.3** (Erdős Problem 985 for large primes). There is `p₀` such that every prime
`p ≥ p₀` has a prime `q < p` that is a primitive root modulo `p`. -/
theorem erdos_985_of_large :
    ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  Main.erdos_985_of_large zeroFree

end Vinogradov
