/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.PermutationClasses
public import BlockIdentities.Tensor.SectorDotClasses
public import BlockIdentities.Tensor.PowerClasses

/-! Literal finite products of the three cyclic orientations. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The actual three tensor factors in cyclic symmetrization. -/
def cyclicProduct (a : TensorClass K) : TensorClass K :=
  a * cycleClass a * cycleClass (cycleClass a)

@[simp] theorem cyclicProduct_tensorClass (A : FiniteTensor K) :
    cyclicProduct (tensorClass A) = tensorClass (symmetrize A) := rfl

@[simp] theorem cyclicProduct_one : cyclicProduct (1 : TensorClass K) = 1 := by
  simp [cyclicProduct]

theorem cyclicProduct_mul (a b : TensorClass K) :
    cyclicProduct (a * b) = cyclicProduct a * cyclicProduct b := by
  simp only [cyclicProduct, cycleClass_mul]
  ring

theorem cyclicProduct_pow (a : TensorClass K) (n : ℕ) :
    cyclicProduct (a ^ n) = cyclicProduct a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, cyclicProduct_mul, ih, pow_succ]

theorem cyclicProduct_prod {ι : Type*} (s : Finset ι) (a : ι → TensorClass K) :
    cyclicProduct (∏ i ∈ s, a i) = ∏ i ∈ s, cyclicProduct (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, cyclicProduct_mul, ih]

@[simp] theorem cyclicProduct_natCast (n : ℕ) :
    cyclicProduct (n : TensorClass K) = ((n ^ 3 : ℕ) : TensorClass K) := by
  simp only [cyclicProduct, cycleClass_natCast, Nat.cast_pow]
  ring

theorem ClassDegenerates.cyclicProduct {a b : TensorClass K}
    (h : ClassDegenerates a b) : ClassDegenerates (cyclicProduct a) (cyclicProduct b) :=
  (h.mul h.cycle).mul h.cycle.cycle

/-- Products of square dimensions agree with actual matrix tensor products. -/
theorem matrixClass_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ) :
    matrixClass (K := K) (∏ i ∈ s, n i) = ∏ i ∈ s, matrixClass (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, matrixClass_one]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, matrixClass_mul, ih]

/-- Permuting a product and taking its three orientations balances the rectangular
factor to the genuine square tensor of its volume. -/
theorem cyclicProduct_permute_product_matrixShape (π : LegPermutation)
    (A : FiniteTensor K) (D : MatrixShape) :
    cyclicProduct (tensorClass (permute π (product A D.tensor))) =
      tensorClass (symmetrize (permute π A)) * matrixClass D.volume := by
  rw [tensorClass_permute_product, cyclicProduct_mul,
    cyclicProduct_tensorClass, cyclicProduct_tensorClass,
    tensorClass_symmetrize_permute_matrixShape]

/-- The three dot orientations multiply to square matrix dimension M. -/
theorem cyclicProduct_dotTensor (M : ℕ) (hM : 1 ≤ M) :
    cyclicProduct (classOf (dotTensor (K := K) M)) = matrixClass M := by
  change cyclicProduct (tensorClass (FiniteTensor.ofTensor (dotTensor (K := K) M))) = _
  rw [cyclicProduct_tensorClass]
  exact symmetrize_dotTensor_class M hM
end BlockIdentities.Square
