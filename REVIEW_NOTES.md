# Review cases

These are constructed examples, not reviews performed for an employer. All
variables below are natural numbers. The corrections are in the named Lean
theorems; the counterexamples and quantifier examples are in `ReviewCases.lean`.

## A. Natural-number subtraction

**Intended claim:** subtracting `b` from `a` and adding it back restores `a`.

**Problem:** natural-number subtraction stops at zero. Without `b ≤ a`,
`(a - b) + b = a` is false. At `a = 0`, `b = 1`, the left side is `1`.
`subtraction_counterexample` verifies this failure.

**Correction:** `sub_add_restore (a b : ℕ) (h : b ≤ a)` proves
`(a - b) + b = a`. The ordering condition includes equality and the zero case.

## B. Missing modulus condition

**Intended claim:** `a % m < m`.

**Problem:** modulus zero is allowed as an input in Lean; `a % 0 = a`.
For `a = 1`, `m = 0`, the proposed inequality is `1 < 0`.
`modulus_zero_counterexample` verifies that it is false.

**Correction:** `remainder_spec (a m : ℕ) (hm : 0 < m)` proves both
`a % m < m` and `a = a % m + m * (a / m)`. Its first component is the corrected
bound. Modulus one is included; modulus zero is excluded explicitly.

## C. Cancellation by zero

**Intended claim:** `a * c = b * c` implies `a = b`.

**Problem:** multiplication by zero loses the original value.
`cancellation_zero_counterexample` proves that `0 * 0 = 1 * 0` while `0 ≠ 1`.

**Correction:** `mul_cancel_right_iff (a b c : ℕ) (hc : c ≠ 0)` proves
`a * c = b * c ↔ a = b`. Over natural numbers the nonzero condition makes `c`
positive, so cancellation applies. It does not require `a` or `b` to be nonzero.

## D. An existential statement is too weak

**Intended claim:** `∀ n : ℕ, sumOdds n = n ^ 2` for the specified recursive
sum of the first `n` odd numbers.

**Problem:** `∃ n : ℕ, sumOdds n = n ^ 2` establishes only one successful input.
`sumOdds_weak_spec` proves this at zero and says nothing about other inputs.

**Formal gap:** the constant-zero candidate also satisfies the existential
statement (`zero_candidate_weak_spec`) but fails the universal statement at
one (`zero_candidate_not_universal`). Thus the existential shape cannot certify
an arbitrary candidate for this specification. This does not refute the intended
claim about `sumOdds`.

**Correction:** `sumOdds_square (n : ℕ)` proves `sumOdds n = n ^ 2` for every
natural number by explicit induction. The base case checks zero. The successor
case adds `2 * n + 1` and proves that the result is `(n + 1) ^ 2`.
