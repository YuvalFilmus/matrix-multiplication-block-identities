/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueProductList
public import BlockIdentities.Tensor.ValueCopiesBound
public import BlockIdentities.Tensor.ValueCopiesLower
public import BlockIdentities.Tensor.ConstructedCyclicity

/-! The actual finite value inequality underlying general extraction. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem extraction_finite_value_bound (A : NonzeroTensor K)
    (L : List (NonzeroTensor K))
    (hL : ∀ B ∈ L, cycleClass (tensorClass B.val) = tensorClass B.val)
    (n a b u h : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : 1 ≤ u) (hh : 1 ≤ h)
    (hconvert : AsymptoticallyRestricts
      (copies u (product (power (symmetrize A.val) n) (square a)))
      (copies h (product (square b) (NonzeroTensor.tensorProductList L).val))) :
    (h : ℝ) * (b : ℝ) ^ Arithmetic.formalOmega K * (L.map valueAtOmega).prod ≤
      (u : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega A ^ (3 * n) *
        (a : ℝ) ^ Arithmetic.formalOmega K := by
  let ρ : Set.Icc (2 : ℝ) 3 :=
    ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  let C := A.symmetrize.power n
  let Q := NonzeroTensor.tensorProductList L
  let P := C.product (nonzeroSquare a ha)
  let R := (nonzeroSquare b hb).product Q
  have hC : cycleClass (tensorClass C.val) = tensorClass C.val :=
    power_cycleClass_fixed (symmetrize_cycleClass_fixed A.val) n
  have hQ := tensorProductList_cycleClass_fixed L hL
  have hP := product_square_cycleClass_fixed hC a
  have hR : cycleClass (tensorClass R.val) = tensorClass R.val :=
    product_cycleClass_fixed (by
      change cycleClass (tensorClass (square (K := K) b)) = tensorClass (square b)
      rw [tensorClass_square_eq, cycleClass_matrixClass]) hQ
  have hm := valueAtOmega_mono_of_asymptoticallyRestricts (P.copies u hu) (R.copies h hh)
    (copies_cycleClass_fixed hP u) (copies_cycleClass_fixed hR h) hconvert
  have hupper := valueAtOmega_copies_le P hP u hu
  have hlower := mul_value_le_value_copies ρ R h hh
  change (h : ℝ) * valueAtOmega R ≤ valueAtOmega (R.copies h hh) at hlower
  have hPv : valueAtOmega P =
      (a : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega A ^ (3 * n) := by
    rw [valueAtOmega_product_square C hC a ha]
    change (a : ℝ) ^ Arithmetic.formalOmega K * value ρ (A.symmetrize.power n) = _
    rw [value_power ρ A.symmetrize n hn, value_symmetrize ρ A, ← pow_mul]
    rfl
  have hRv : valueAtOmega R = (b : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega Q := by
    have heq : tensorClass R.val = tensorClass (Q.product (nonzeroSquare b hb)).val := by
      simp only [R, NonzeroTensor.product, tensorClass_product_eq]
      exact mul_comm _ _
    have hv := value_eq_of_tensorClass_eq ρ R (Q.product (nonzeroSquare b hb)) heq
    change valueAtOmega R = valueAtOmega (Q.product (nonzeroSquare b hb)) at hv
    exact hv.trans (valueAtOmega_product_square Q hQ b hb)
  have hprod := valueAtOmega_tensorProductList L hL
  have hfactor : 0 ≤ (h : ℝ) * (b : ℝ) ^ Arithmetic.formalOmega K := by positivity
  calc
    _ ≤ (h : ℝ) * (b : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega Q :=
      mul_le_mul_of_nonneg_left hprod hfactor
    _ = (h : ℝ) * valueAtOmega R := by rw [hRv]; ring
    _ ≤ (u : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega P :=
      (hlower.trans hm).trans hupper
    _ = _ := by rw [hPv]; ring

end BlockIdentities.Square
