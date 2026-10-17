# Lean Arithmetic Lab

A learning project in Lean 4 about arithmetic, recursive algorithms, and modular
equations. The development starts with finite sums, then moves to a division
algorithm, loop invariants, and uniqueness of solutions.

- `LeanArithmeticLab/Arithmetic.lean`: parity, divisibility, remainders, and
  cancellation over natural numbers.
- `LeanArithmeticLab/FiniteSums.lean`: recursive sums of natural numbers, odd numbers,
  and squares, with formulas established by induction.
- `LeanArithmeticLab/Division.lean`: division by repeated subtraction, a
  termination argument, an accumulator invariant, and a unique quotient and remainder.
- `LeanArithmeticLab/Congruences.lean`: affine maps modulo a number and a unique
  bounded solution to two congruences with coprime moduli.
- `LeanArithmeticLab/Counterexamples.lean`: examples showing why hypotheses,
  bounds, and quantifiers matter.
- `LeanArithmeticLab/AxiomAudit.lean`: enforced checks on theorem dependencies.

[NOTES.md](NOTES.md) connects the examples to the statements they help explain.
The mathematics is standard; this project is a worked formalization for study.

## Setup and verification

Install Git, Python 3.10 or later, and [Elan](https://github.com/leanprover/elan#installation).
Make `lake` and `python` available on your PATH. Elan selects Lean 4.35.0 from
`lean-toolchain`. Mathlib is pinned to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (release v4.35.0), with transitive
dependencies recorded in `lake-manifest.json`.

```sh
git clone https://github.com/Ritik13012002/lean4-arithmetic-lab.git
cd lean4-arithmetic-lab
lake exe cache get Mathlib.Algebra.Ring.Nat Mathlib.Order.Monotone.Basic Mathlib.Tactic.Ring Mathlib.Data.Nat.ModEq
python verify.py
```

The cache command retrieves the imported Mathlib modules and their dependencies.
On systems where Python is named `python3`, use `python3 verify.py`.

To rebuild the project from clean local outputs, keeping the dependency cache:

```sh
lake clean lean4-arithmetic-lab
python verify.py
```

`python verify.py` builds the root and every module under `LeanArithmeticLab/`,
checks project sources for unfinished terms, and runs a fresh axiom audit over
all of those modules. It fails on any failed check. The audit discovers theorem
declarations by their defining module, including private and generated theorems.
It rejects project axioms and transitive dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`.

The source check is conservative and may flag forbidden words in comments.
The dependency audit does not establish that an English description matches its
formal statement. Read the types and assumptions alongside the notes.

The division algorithm favors a simple invariant over speed: it performs one
subtraction per quotient step. It is not a replacement for Lean's efficient
built-in division.

GitHub Actions runs the same verification: [CI workflow](https://github.com/Ritik13012002/lean4-arithmetic-lab/actions/workflows/ci.yml).

Code and examples were generated with Codex.
