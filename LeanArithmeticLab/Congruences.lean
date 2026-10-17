module

public import Mathlib.Data.Nat.ModEq

public section

namespace LeanArithmeticLab

/-- An affine map modulo `m` distinguishes canonical representatives when its
multiplier is coprime to `m`. Nonzero alone would not suffice. -/
theorem affine_mod_injective (m c d a b : ℕ) (hc : m.Coprime c)
    (ha : a < m) (hb : b < m) :
    (c * a + d) % m = (c * b + d) % m ↔ a = b := by
  constructor
  · intro h
    have hAffine : c * a + d ≡ c * b + d [MOD m] := h
    have hProduct : c * a ≡ c * b [MOD m] :=
      Nat.ModEq.add_right_cancel' d hAffine
    have hInput : a ≡ b [MOD m] := hProduct.cancel_left_of_coprime hc
    exact hInput.eq_of_lt_of_lt ha hb
  · intro h
    simp only [h]

/-- Coprime positive moduli give one representative in the half-open interval
`[0, m * n)` for every pair of residues. -/
theorem crt_exists_unique (m n a b : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    ∃! x : ℕ, x < m * n ∧ x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  let x := Nat.chineseRemainder hcop a b
  have hx : (x : ℕ) < m * n :=
    Nat.chineseRemainder_lt_mul hcop a b (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)
  refine ⟨x, ⟨hx, x.property⟩, ?_⟩
  intro y hy
  have hym : y ≡ x [MOD m] := hy.2.1.trans x.property.1.symm
  have hyn : y ≡ x [MOD n] := hy.2.2.trans x.property.2.symm
  have hProduct : y ≡ x [MOD m * n] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hym, hyn⟩
  exact hProduct.eq_of_lt_of_lt hy.1 hx

end LeanArithmeticLab
