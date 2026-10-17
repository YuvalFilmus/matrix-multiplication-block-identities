/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.PowerClasses
public import BlockIdentities.Tensor.MatrixSymmetries

/-! Cyclic classes for the actual constructions used in extraction. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem product_cycleClass_fixed {A B : FiniteTensor K}
    (hA : cycleClass (tensorClass A) = tensorClass A)
    (hB : cycleClass (tensorClass B) = tensorClass B) :
    cycleClass (tensorClass (product A B)) = tensorClass (product A B) := by
  simp only [tensorClass_product_eq, cycleClass_mul, hA, hB]

theorem power_cycleClass_fixed {A : FiniteTensor K}
    (hA : cycleClass (tensorClass A) = tensorClass A) (n : ℕ) :
    cycleClass (tensorClass (power A n)) = tensorClass (power A n) := by
  simp only [tensorClass_power_eq, cycleClass_pow, hA]

theorem copies_cycleClass_fixed {A : FiniteTensor K}
    (hA : cycleClass (tensorClass A) = tensorClass A) (n : ℕ) :
    cycleClass (tensorClass (copies n A)) = tensorClass (copies n A) := by
  simp only [tensorClass_copies_eq, cycleClass_mul, cycleClass_natCast, hA]

end BlockIdentities.Square
