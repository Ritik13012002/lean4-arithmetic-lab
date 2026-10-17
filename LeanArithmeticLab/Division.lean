module

public import LeanArithmeticLab.Arithmetic
public import Mathlib.Tactic.Ring

public section

namespace LeanArithmeticLab

/-- Subtract the divisor from the remainder while incrementing the quotient. -/
@[expose] def divideAux (m r q : ℕ) : ℕ × ℕ :=
  if 0 < m ∧ m ≤ r then divideAux m (r - m) (q + 1) else (q, r)
termination_by r
decreasing_by omega

@[expose] def divide (n m : ℕ) : ℕ × ℕ := divideAux m n 0

/-- The represented number is unchanged, even with a nonzero initial quotient. -/
theorem divideAux_invariant (m r q : ℕ) :
    m * (divideAux m r q).1 + (divideAux m r q).2 = m * q + r := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    rw [divideAux]
    split
    · rename_i h
      rw [ih (r - m) (by omega)]
      have hr : r - m + m = r := Nat.sub_add_cancel h.2
      calc
        m * (q + 1) + (r - m) = m * q + ((r - m) + m) := by ring
        _ = m * q + r := by rw [hr]
    · rfl

theorem divideAux_remainder_lt (m r q : ℕ) (hm : 0 < m) :
    (divideAux m r q).2 < m := by
  induction r using Nat.strong_induction_on generalizing q with
  | h r ih =>
    rw [divideAux]
    split
    · rename_i h
      exact ih (r - m) (by omega) (q + 1)
    · simp only
      omega

theorem divide_spec (n m : ℕ) (hm : 0 < m) :
    n = m * (divide n m).1 + (divide n m).2 ∧ (divide n m).2 < m := by
  constructor
  · simpa only [divide, Nat.mul_zero, Nat.zero_add] using
      (divideAux_invariant m n 0).symm
  · exact divideAux_remainder_lt m n 0 hm

/-- Reconstruction and the strict remainder bound determine both outputs. -/
theorem division_pair_unique (n m q r : ℕ) (hm : 0 < m)
    (h : n = m * q + r) (hr : r < m) : (q, r) = (n / m, n % m) := by
  subst n
  apply Prod.ext
  · rw [Nat.add_comm (m * q) r, Nat.add_mul_div_left r q hm,
      Nat.div_eq_of_lt hr, Nat.zero_add]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]

theorem divide_eq_div_mod (n m : ℕ) : divide n m = (n / m, n % m) := by
  by_cases hm : m = 0
  · subst m
    simp [divide, divideAux]
  · have hs := divide_spec n m (Nat.pos_of_ne_zero hm)
    exact division_pair_unique n m _ _ (Nat.pos_of_ne_zero hm) hs.1 hs.2

theorem division_exists_unique (n m : ℕ) (hm : 0 < m) :
    ∃! p : ℕ × ℕ, n = m * p.1 + p.2 ∧ p.2 < m := by
  refine ⟨divide n m, divide_spec n m hm, ?_⟩
  intro p hp
  exact (division_pair_unique n m p.1 p.2 hm hp.1 hp.2).trans
    (divide_eq_div_mod n m).symm

end LeanArithmeticLab
