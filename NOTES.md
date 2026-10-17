# Notes on arithmetic and assumptions

These worked examples explore what changes when a hypothesis or part of a
specification is missing. Variables are natural numbers unless stated otherwise.
Counterexamples are checked in `Counterexamples.lean`.

## 1. Subtracting and adding back

The unrestricted statement `(a - b) + b = a` fails because subtraction in `ℕ`
stops at zero. At `a = 0`, `b = 1`, the left side is `1`.
`subtraction_counterexample` checks this failure.

`sub_add_restore` establishes the equation under `b ≤ a`, including equality
and zero. Changing the number type would change the problem.

## 2. Remainder bounds

The statement `a % m < m` needs `0 < m`. Lean defines `a % 0 = a`, so at
`a = 1`, `m = 0` the proposed bound is false (`modulus_zero_counterexample`).

`remainder_spec` includes both the bound and the reconstruction
`a = a % m + m * (a / m)`. Modulus one is allowed.

## 3. Ordinary cancellation

From `a * c = b * c`, one cannot conclude `a = b` when `c = 0`.
`cancellation_zero_counterexample` checks `0 * 0 = 1 * 0` and `0 ≠ 1`.

`mul_cancel_right_iff` requires `c ≠ 0`. It puts no nonzero restriction on
`a` or `b`.

## 4. One input versus every input

`∃ n, sumOdds n = n ^ 2` is much weaker than the intended universal formula.
`sumOdds_weak_spec` establishes the existential statement at zero.

The constant-zero function also satisfies that shape (`zero_candidate_weak_spec`)
but fails the universal version at one (`zero_candidate_not_universal`). This
demonstrates a gap in the specification, not a failure of `sumOdds`.
`sumOdds_square` establishes the intended formula for every `n` by induction.

## 5. Division needs an invariant and a bound

`divideAux m r q` repeatedly changes `(q, r)` to `(q + 1, r - m)` when
`0 < m` and `m ≤ r`. The termination measure is `r`; both conditions matter
when establishing that it decreases.

`divideAux_invariant` keeps `m * q + r` constant. Its induction hypothesis
allows any accumulator `q`, because the recursive call changes that argument.
`divideAux_remainder_lt` separately establishes the stopping bound when `m > 0`.

Reconstruction alone cannot determine the output: `7 = 3 * 1 + 4` and
`7 = 3 * 2 + 1` (`unbounded_remainder_counterexample`). The strict bound `r < m`
rules out the first pair. `division_pair_unique` identifies every valid pair
with `(n / m, n % m)`, and `division_exists_unique` combines existence and uniqueness.

`divide_eq_div_mod` covers all inputs, including divisor zero, where the
algorithm returns `(0, n)`. A bounded-remainder specification cannot hold there.

## 6. Modular cancellation needs more than nonzero

Modulo six, `2 * 1` and `2 * 4` have the same remainder. The inputs are distinct
and both below six; the multiplier is nonzero. This is checked by
`modular_cancellation_counterexample`.

`affine_mod_injective` assumes the multiplier `c` is coprime to `m`. It first
cancels the common offset, then the multiplier, to obtain congruent inputs.
The bounds `a < m` and `b < m` turn congruence into equality. Without those
bounds, equal remainders would identify residue classes rather than exact inputs.

## 7. Two congruences and one representative

`crt_exists_unique` combines the congruences `x ≡ a [MOD m]` and `x ≡ b [MOD n]`.
Positive coprime moduli guarantee a unique solution in `0 ≤ x < m * n`.
The construction uses Mathlib's Chinese remainder theorem; the uniqueness
argument combines congruences and then uses the bound.

For noncoprime moduli, arbitrary residues need not be compatible.
`incompatible_residues` rules out an odd number that is also divisible by four.
The theorem does not claim that every noncoprime system is unsolvable.

## 8. A polynomial formula with natural division

`six_mul_sumSquares` establishes
`6 * sumSquares n = n * (n + 1) * (2 * n + 1)` by induction. Multiplying first
keeps the algebra polynomial. `six_dvd_square_sum_numerator` records exact
divisibility, and `sumSquares_eq_polynomial` gives the division form.

Dividing one factor early can change a natural-number result:
`2 * (3 / 2) ≠ (2 * 3) / 2` (`premature_division_counterexample`). A field-style
rearrangement of division would miss the truncation.
