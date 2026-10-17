module

public import Mathlib.Algebra.Ring.Nat

public section

namespace LeanProofReview

/-- Exactly one of two consecutive natural numbers has remainder one modulo two. -/
theorem consecutive_parity (n : ℕ) : n % 2 + (n + 1) % 2 = 1 := by
  omega

theorem two_dvd_consecutive_product (n : ℕ) : 2 ∣ n * (n + 1) := by
  have h := consecutive_parity n
  by_cases hn : n % 2 = 0
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hn) (n + 1)
  · have hs : (n + 1) % 2 = 0 := by omega
    exact Nat.dvd_mul_left_of_dvd (Nat.dvd_of_mod_eq_zero hs) n

/-- Division gives both a bounded remainder and an exact reconstruction. -/
theorem remainder_spec (a m : ℕ) (hm : 0 < m) :
    a % m < m ∧ a = a % m + m * (a / m) := by
  exact ⟨Nat.mod_lt a hm, (Nat.mod_add_div a m).symm⟩

theorem sub_add_restore (a b : ℕ) (h : b ≤ a) : (a - b) + b = a := by
  omega

theorem mul_cancel_right_iff (a b c : ℕ) (hc : c ≠ 0) :
    a * c = b * c ↔ a = b := by
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) h
  · intro h
    simp only [h]

end LeanProofReview
