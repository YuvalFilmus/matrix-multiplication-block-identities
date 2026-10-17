/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.RectangularProgramRank
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual finite Kronecker matrix rank products over every field. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {F : Type*} [Field F]

/-- Reindex the true tensor product of two coefficient rank decompositions. -/
theorem rectangular_matrix_rankAtMost_product {a b c A B C R S : ℕ}
    (hT : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) a b c) R)
    (hU : Tensor.RankAtMost (matrixMultiplicationTensor (K := F) A B C) S) :
    Tensor.RankAtMost (matrixMultiplicationTensor (K := F) (a * A) (b * B) (c * C))
      (R * S) := by
  classical
  let ea : Fin (a * A) ≃ Fin a × Fin A := finProdFinEquiv.symm
  let eb : Fin (b * B) ≃ Fin b × Fin B := finProdFinEquiv.symm
  let ec : Fin (c * C) ≃ Fin c × Fin C := finProdFinEquiv.symm
  have hp := Tensor.matrixCoefficients_product_rank hT hU
  have hr := hp.pullback (fun x : Fin (a * A) × Fin (b * B) => (ea x.1, eb x.2))
    (fun y : Fin (b * B) × Fin (c * C) => (eb y.1, ec y.2)) (fun z : Fin (c * C) × Fin (a * A) => (ec z.1, ea z.2))
  have heq : Tensor.pullback (fun x : Fin (a * A) × Fin (b * B) => (ea x.1, eb x.2))
      (fun y : Fin (b * B) × Fin (c * C) => (eb y.1, ec y.2)) (fun z : Fin (c * C) × Fin (a * A) => (ec z.1, ea z.2))
      (Tensor.matrixCoefficients (K := F) (Fin a × Fin A) (Fin b × Fin B) (Fin c × Fin C)) =
      matrixMultiplicationTensor (K := F) (a * A) (b * B) (c * C) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.matrixCoefficients, matrixMultiplicationTensor,
      ea.injective.eq_iff, eb.injective.eq_iff, ec.injective.eq_iff]
  rw [heq] at hr
  exact hr
end BlockIdentities.Arithmetic
