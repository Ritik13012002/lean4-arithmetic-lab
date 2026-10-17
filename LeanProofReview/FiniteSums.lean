module

public import LeanProofReview.Arithmetic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Ring

public section

namespace LeanProofReview

@[expose] def sumFirst : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFirst n + (n + 1)

@[expose] def sumOdds : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumOdds n + (2 * n + 1)

theorem twice_sumFirst (n : ℕ) : 2 * sumFirst n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      2 * sumFirst (n + 1) = 2 * sumFirst n + 2 * (n + 1) := by
        simp only [sumFirst, Nat.mul_add]
      _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
      _ = (n + 1) * ((n + 1) + 1) := by ring

theorem sumOdds_square (n : ℕ) : sumOdds n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      sumOdds (n + 1) = sumOdds n + (2 * n + 1) := rfl
      _ = n ^ 2 + (2 * n + 1) := by rw [ih]
      _ = (n + 1) ^ 2 := by ring

theorem sumFirst_eq_half_product (n : ℕ) : sumFirst n = n * (n + 1) / 2 := by
  rw [← twice_sumFirst]
  omega

theorem sumFirst_strictMono : StrictMono sumFirst := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sumFirst]
  omega

/-- The two recursive sums agree with the same quadratic expression. -/
theorem sumOdds_add_index (n : ℕ) : sumOdds n + n = 2 * sumFirst n := by
  rw [sumOdds_square, twice_sumFirst]
  ring

end LeanProofReview
