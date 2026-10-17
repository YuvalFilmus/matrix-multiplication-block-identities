/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueMatrixFactorEquality
public import BlockIdentities.Tensor.ValueMonotonicity

/-! Bound common copies by supplying them from a matrix factor. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem degenerates_product_square_to_copies (A : FiniteTensor K) (b : ℕ) :
    Degenerates (product A (square b)) (copies b A) := by
  apply (classDegenerates_tensorClass_iff _ _).1
  rw [tensorClass_product_eq, tensorClass_copies_eq, tensorClass_square_eq]
  apply ClassDegenerates.of_le
  calc
    (b : TensorClass K) * tensorClass A = tensorClass A * (b : TensorClass K) := mul_comm _ _
    _ ≤ tensorClass A * matrixClass b := mul_mono le_rfl (natCast_le_matrixClass b)

theorem valueAtOmega_copies_le [IsAlgClosed K]
    (A : NonzeroTensor K)
    (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    (b : ℕ) (hb : 1 ≤ b) :
    valueAtOmega (A.copies b hb) ≤ (b : ℝ) ^ Arithmetic.formalOmega K * valueAtOmega A := by
  have hle := value_mono_of_degeneration
    ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
    (A.product (nonzeroSquare b hb)) (A.copies b hb)
    (degenerates_product_square_to_copies A.val b)
  change valueAtOmega (A.copies b hb) ≤ valueAtOmega (A.product (nonzeroSquare b hb)) at hle
  exact hle.trans_eq (valueAtOmega_product_square A hcycle b hb)

end BlockIdentities.Square
