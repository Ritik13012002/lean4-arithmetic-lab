module

public import LeanArithmeticLab.FiniteSums
public import LeanArithmeticLab.Division
public import LeanArithmeticLab.Congruences

public section

namespace LeanArithmeticLab.Counterexamples

theorem subtraction_counterexample : (0 - 1 : ℕ) + 1 ≠ 0 := by decide

theorem modulus_zero_counterexample : ¬ ((1 : ℕ) % 0 < 0) := by decide

theorem cancellation_zero_counterexample :
    (0 : ℕ) * 0 = 1 * 0 ∧ (0 : ℕ) ≠ 1 := by decide

/-- This is true but certifies only one input of the intended sum-of-odds specification. -/
theorem sumOdds_weak_spec : ∃ n : ℕ, sumOdds n = n ^ 2 := by
  exact ⟨0, rfl⟩

/-- Even the constant-zero candidate passes that existential specification. -/
theorem zero_candidate_weak_spec : ∃ n : ℕ, (fun _ : ℕ => 0) n = n ^ 2 := by
  exact ⟨0, rfl⟩

theorem zero_candidate_not_universal : ¬ ∀ n : ℕ, (fun _ : ℕ => 0) n = n ^ 2 := by
  intro h
  simpa using h 1

/-- Both inputs are below the modulus, and the multiplier is nonzero. -/
theorem modular_cancellation_counterexample :
    (2 * 1 : ℕ) % 6 = (2 * 4 : ℕ) % 6 ∧ (1 : ℕ) ≠ 4 := by decide

/-- Reconstruction alone allows a remainder larger than the divisor. -/
theorem unbounded_remainder_counterexample :
    (7 : ℕ) = 3 * 1 + 4 ∧ (7 : ℕ) = 3 * 2 + 1 ∧
      ((1, 4) : ℕ × ℕ) ≠ (2, 1) := by decide

theorem incompatible_residues : ¬ ∃ x : ℕ, x ≡ 1 [MOD 2] ∧ x ≡ 0 [MOD 4] := by
  rintro ⟨x, h₂, h₄⟩
  change x % 2 = 1 % 2 at h₂
  change x % 4 = 0 % 4 at h₄
  omega

/-- Division over natural numbers cannot be moved across a factor freely. -/
theorem premature_division_counterexample : (2 : ℕ) * (3 / 2) ≠ (2 * 3) / 2 := by
  decide

end LeanArithmeticLab.Counterexamples
