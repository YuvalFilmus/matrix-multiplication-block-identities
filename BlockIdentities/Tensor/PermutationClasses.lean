/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueSymmetries
public import BlockIdentities.Tensor.RectangularClasses
public import BlockIdentities.Tensor.ConstructedCyclicity

/-! The six actual leg permutations on genuine tensor classes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

def permuteClass (π : LegPermutation) (a : TensorClass K) : TensorClass K :=
  match π with
  | .xyz => a
  | .xzy => swapClass a
  | .yzx => cycleClass a
  | .zxy => cycleClass (cycleClass a)
  | .zyx => cycleClass (swapClass a)
  | .yxz => cycleClass (cycleClass (swapClass a))

theorem tensorClass_permute (π : LegPermutation) (A : FiniteTensor K) :
    tensorClass (permute π A) = permuteClass π (tensorClass A) := by
  cases π with
  | xyz => rfl
  | xzy => exact (swapClass_tensorClass A).symm
  | yzx => exact (cycleClass_tensorClass A).symm
  | zxy =>
    change tensorClass (permute .yzx (permute .yzx A)) = cycleClass (cycleClass (tensorClass A))
    rw [← cycleClass_tensorClass, ← cycleClass_tensorClass]
  | zyx =>
    change tensorClass (permute .yzx (permute .xzy A)) = cycleClass (swapClass (tensorClass A))
    rw [← cycleClass_tensorClass, ← swapClass_tensorClass]
  | yxz =>
    change tensorClass (permute .yzx (permute .yzx (permute .xzy A))) =
      cycleClass (cycleClass (swapClass (tensorClass A)))
    rw [← cycleClass_tensorClass, ← cycleClass_tensorClass, ← swapClass_tensorClass]

theorem permuteClass_mul (π : LegPermutation) (a b : TensorClass K) :
    permuteClass π (a * b) = permuteClass π a * permuteClass π b := by
  cases π <;> simp only [permuteClass, cycleClass_mul, swapClass_mul]

theorem tensorClass_permute_product (π : LegPermutation) (A B : FiniteTensor K) :
    tensorClass (permute π (product A B)) =
      tensorClass (permute π A) * tensorClass (permute π B) := by
  simp only [tensorClass_permute, tensorClass_product_eq, permuteClass_mul]

theorem ClassDegenerates.permute {a b : TensorClass K} (h : ClassDegenerates a b)
    (π : LegPermutation) : ClassDegenerates (permuteClass π a) (permuteClass π b) := by
  cases π with
  | xyz => exact h
  | xzy => exact h.swap
  | yzx => exact h.cycle
  | zxy => exact h.cycle.cycle
  | zyx => exact h.swap.cycle
  | yxz => exact h.swap.cycle.cycle

theorem symmetrize_product_class (A B : FiniteTensor K) :
    tensorClass (symmetrize (product A B)) =
      tensorClass (symmetrize A) * tensorClass (symmetrize B) := by
  simp only [tensorClass_symmetrize_eq, tensorClass_product_eq, cycleClass_mul]
  ring

theorem tensorClass_symmetrize_permute (π : LegPermutation) (A : FiniteTensor K) :
    tensorClass (symmetrize (permute π A)) = permuteClass π (tensorClass (symmetrize A)) := by
  have hA := symmetrize_cycleClass_fixed A
  have hS := symmetrize_cycleClass_fixed (permute .xzy A)
  rw [tensorClass_symmetrize_swap] at hS
  cases π with
  | xyz => rfl
  | xzy => exact tensorClass_symmetrize_swap A
  | yzx => simpa only [permuteClass, hA] using tensorClass_symmetrize_cycle A
  | zxy =>
    change tensorClass (symmetrize (permute .yzx (permute .yzx A))) =
      cycleClass (cycleClass (tensorClass (symmetrize A)))
    rw [tensorClass_symmetrize_cycle, tensorClass_symmetrize_cycle, hA, hA]
  | zyx =>
    change tensorClass (symmetrize (permute .yzx (permute .xzy A))) =
      cycleClass (swapClass (tensorClass (symmetrize A)))
    rw [tensorClass_symmetrize_cycle, tensorClass_symmetrize_swap, hS]
  | yxz =>
    change tensorClass (symmetrize (permute .yzx (permute .yzx (permute .xzy A)))) =
      cycleClass (cycleClass (swapClass (tensorClass (symmetrize A))))
    rw [tensorClass_symmetrize_cycle, tensorClass_symmetrize_cycle, tensorClass_symmetrize_swap, hS, hS]

theorem tensorClass_symmetrize_permute_matrixShape (π : LegPermutation) (D : MatrixShape) :
    tensorClass (symmetrize (permute π (D.tensor (K := K)))) = matrixClass D.volume := by
  rw [tensorClass_symmetrize_permute, tensorClass_symmetrize_matrixShape]
  cases π <;> simp only [permuteClass, cycleClass_matrixClass, swapClass_matrixClass]

end BlockIdentities.Square
