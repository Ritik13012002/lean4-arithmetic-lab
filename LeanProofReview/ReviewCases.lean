module

public import LeanProofReview.FiniteSums

public section

namespace LeanProofReview.ReviewCases

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

end LeanProofReview.ReviewCases
