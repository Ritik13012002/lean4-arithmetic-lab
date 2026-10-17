# lean4-proof-review

This project contains Lean 4 proofs for arithmetic and finite sums. It also
contains four constructed proof-review examples. These are standard mathematical
results, not new discoveries or records of work for an employer.

- `LeanProofReview/Arithmetic.lean`: parity, divisibility, remainders, subtraction,
  and cancellation, with the required assumptions.
- `LeanProofReview/FiniteSums.lean`: recursive sums and their formulas, proved by
  induction, plus consequences connecting the sums.
- `LeanProofReview/ReviewCases.lean`: checked counterexamples and a quantifier gap.
- `LeanProofReview/AxiomAudit.lean`: an enforced audit of transitive axiom dependencies.

See [REVIEW_NOTES.md](REVIEW_NOTES.md) for the four cases.

## Setup and verification

Install Git, Python 3.10 or later, and [Elan](https://github.com/leanprover/elan#installation).
Make `lake` and `python` available on your PATH. Elan selects Lean 4.35.0 from
`lean-toolchain`. Mathlib is pinned to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (release v4.35.0), with transitive
dependencies recorded in `lake-manifest.json`.

```sh
git clone https://github.com/Ritik13012002/lean4-proof-review.git
cd lean4-proof-review
lake exe cache get Mathlib.Algebra.Ring.Nat Mathlib.Order.Monotone.Basic Mathlib.Tactic.Ring
python verify.py
```

The cache command retrieves the imported Mathlib modules and their dependencies.
On systems where Python is named `python3`, use `python3 verify.py`.

To rebuild the project from clean local outputs, keeping the dependency cache:

```sh
lake clean lean4-proof-review
python verify.py
```

`python verify.py` builds the root and every module under `LeanProofReview/`,
checks project sources for unfinished proof constructs, and runs a fresh axiom
audit over all of those imported modules. It fails on any failed check. The audit
discovers theorem declarations by their defining module, including private and
generated theorems; it does not rely on a manually maintained theorem list or a
text search. It rejects project axioms and any transitive theorem dependency
outside `propext`, `Classical.choice`, and `Quot.sound`.

The source check is conservative and may also flag forbidden words in comments.
The audit checks proof dependencies, not whether an English description is the
right specification. Read the statements and assumptions alongside the notes.

GitHub Actions runs the same verification: [CI workflow](https://github.com/Ritik13012002/lean4-proof-review/actions/workflows/ci.yml).

Code and review examples were generated with Codex.
