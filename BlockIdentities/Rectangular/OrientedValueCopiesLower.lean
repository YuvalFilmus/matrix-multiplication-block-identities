/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedValueSums

/-! Actual independent-copy lower bounds, without convolution dependencies. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Superadditivity on actual independent sums supplies the full copy factor. -/
theorem mul_orientedValue_le_copies (S : InteriorSupport F) (T : TensorOf F)
    (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * orientedValue S T ≤ orientedValue S (T.copies m hm) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hc : tensorClass (T.copies 1 le_rfl).val = tensorClass T.val := by
      change tensorClass (copies 1 T.val) = _
      rw [tensorClass_copies_eq, Nat.cast_one, one_mul]
    have hv := orientedValue_eq_of_tensorClass_eq S _ _ hc
    simpa only [Nat.cast_one, one_mul] using hv.ge
  | succ m hm ih =>
    let U := T.copies m hm
    have hc : tensorClass (U.sum T).val =
        tensorClass (T.copies (m + 1) (by omega)).val := by
      change tensorClass U.val + tensorClass T.val = tensorClass (copies (m + 1) T.val)
      have hU : U.val = copies m T.val := rfl
      rw [hU, tensorClass_copies_eq, tensorClass_copies_eq, Nat.cast_add, Nat.cast_one]
      ring
    have hv := orientedValue_eq_of_tensorClass_eq S _ _ hc
    change (m : ℝ) * orientedValue S T ≤ orientedValue S U at ih
    have hsum := orientedValue_sum_le S U T
    rw [hv] at hsum
    calc
      ((m + 1 : ℕ) : ℝ) * orientedValue S T =
          (m : ℝ) * orientedValue S T + orientedValue S T := by push_cast; ring
      _ ≤ orientedValue S U + orientedValue S T := by linarith only [ih]
      _ ≤ _ := hsum

end BlockIdentities.Rectangular
