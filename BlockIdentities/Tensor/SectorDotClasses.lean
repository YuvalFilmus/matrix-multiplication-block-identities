/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SeparatorClasses
public import BlockIdentities.Tensor.RectangularClasses

/-! Literal sector masks and their finite dot-product factors. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Retain exactly one second-leg sector of the original tensor. -/
def sectorBlock {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (sy : Y → ι) (i : ι) : Tensor K X Y Z :=
  fun x y z => if sy y = i then T x y z else 0

/-- The dot product has a scalar first leg and two matching M-coordinates. -/
def dotTensor (M : ℕ) : Tensor K PUnit.{1} (Fin M) (Fin M) :=
  fun _ u v => if u = v then 1 else 0

theorem classOf_sectorDotBlock {M : ℕ}
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) (sy : Y → Fin M) (i : Fin M) :
    classOf (sectorDotBlock T sy i) = classOf (sectorBlock T sy i) * classOf (dotTensor (K := K) M) := by
  rw [← classOf_product]
  apply classOf_eq_of_reindex (Equiv.prodUnique X PUnit.{1}).symm (Equiv.refl _) (Equiv.refl _)
  funext x y z
  simp only [Tensor.pullback, Tensor.product, Equiv.prodUnique_symm_apply,
    Equiv.refl_apply, sectorBlock, dotTensor, sectorDotBlock]
  by_cases hs : sy y.1 = i <;> by_cases hu : y.2 = z.2 <;> simp [hs, hu]

theorem classOf_dotTensor (M : ℕ) :
    classOf (dotTensor (K := K) M) = tensorClass (matrix (K := K) 1 1 M) := by
  let e : PUnit.{1} ≃ Fin 1 × Fin 1 := Fintype.equivOfCardEq (by simp)
  change classOf (dotTensor (K := K) M) = classOf (matrixMultiplicationTensor (K := K) 1 1 M)
  apply classOf_eq_of_reindex e (Equiv.uniqueProd (Fin M) (Fin 1)).symm
    (Equiv.prodUnique (Fin M) (Fin 1)).symm
  funext x y z
  have h1 : (e x).2 = (default : Fin 1) := Subsingleton.elim _ _
  have h2 : (default : Fin 1) = (e x).1 := Subsingleton.elim _ _
  simp only [Tensor.pullback, matrixMultiplicationTensor, Equiv.uniqueProd_symm_apply,
    Equiv.prodUnique_symm_apply, dotTensor]
  simp only [h1, h2, true_and, and_true]

/-- The literal dot factor balances to a square matrix of dimension M. -/
theorem symmetrize_dotTensor_class (M : ℕ) (hM : 1 ≤ M) :
    tensorClass (symmetrize (FiniteTensor.ofTensor (dotTensor (K := K) M))) = matrixClass M := by
  let D : MatrixShape := ⟨1, 1, M, Nat.zero_lt_one, Nat.zero_lt_one,
    lt_of_lt_of_le Nat.zero_lt_one hM⟩
  have hd : tensorClass (FiniteTensor.ofTensor (dotTensor (K := K) M)) =
      tensorClass (D.tensor (K := K)) := classOf_dotTensor M
  rw [tensorClass_symmetrize_eq, hd]
  rw [← tensorClass_symmetrize_eq, tensorClass_symmetrize_matrixShape]
  simp only [D, MatrixShape.volume, one_mul]

/-- Disjoint supported summands are exactly the literal masks of their sum. -/
theorem blocks_eq_sectorBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Tensor K X Y Z) (blocks : ι → Tensor K X Y Z) (sy : Y → ι)
    (hsum : T = ∑ i, blocks i)
    (hsupport : ∀ i x y z, blocks i x y z ≠ 0 → sy y = i) (i : ι) :
    blocks i = sectorBlock T sy i := by
  classical
  funext x y z
  by_cases hs : sy y = i
  · have heq : T x y z = ∑ j, blocks j x y z := by
      simpa only [Finset.sum_apply] using congrFun (congrFun (congrFun hsum x) y) z
    have hsumone : (∑ j, blocks j x y z) = blocks i x y z := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_contra hn
        exact hji ((hsupport j x y z hn).symm.trans hs)
      · simp
    simp only [sectorBlock, hs, ite_true]
    exact (heq.trans hsumone).symm
  · have hzero : blocks i x y z = 0 := by
      by_contra hn
      exact hs (hsupport i x y z hn)
    simp only [sectorBlock, hs, ite_false, hzero]

end BlockIdentities.Square
