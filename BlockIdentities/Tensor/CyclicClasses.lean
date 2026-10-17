/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassDegeneration
public import BlockIdentities.Tensor.IsomorphismClasses

/-! Cyclic permutation as an actual action on mutual-restriction classes. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem permute_yzx_mono {A B : FiniteTensor K} (h : A ≤ B) :
    permute .yzx A ≤ permute .yzx B := by
  obtain ⟨Lx, Ly, Lz, h⟩ := h
  refine ⟨Ly, Lz, Lx, ?_⟩
  change Tensor.cyclic A.coeff = Tensor.restrict Ly Lz Lx (Tensor.cyclic B.coeff)
  rw [h]
  exact Tensor.cyclic_restrict Lx Ly Lz B.coeff

/-- Permuting a representative induces the same genuine cyclic operation
on the quotient, because all three restriction maps are permuted with it. -/
def cycleClass : TensorClass K → TensorClass K :=
  Quotient.map (permute .yzx) (by
    intro A B h
    exact ⟨permute_yzx_mono h.1, permute_yzx_mono h.2⟩)

@[simp] theorem cycleClass_tensorClass (A : FiniteTensor K) :
    cycleClass (tensorClass A) = tensorClass (permute .yzx A) := rfl

theorem cycleClass_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : cycleClass (classOf T) = classOf (Tensor.cyclic T) := by
  change tensorClass (permute .yzx (FiniteTensor.ofTensor T)) = _
  rw [← classOf_coeff]
  exact classOf_reindex (Tensor.cyclic T) (Fintype.equivFin Y).symm
    (Fintype.equivFin Z).symm (Fintype.equivFin X).symm

@[simp] theorem cycleClass_three (a : TensorClass K) :
    cycleClass (cycleClass (cycleClass a)) = a := by
  induction a using Quotient.inductionOn with
  | h A => rfl

@[simp] theorem cycleClass_mul (a b : TensorClass K) :
    cycleClass (a * b) = cycleClass a * cycleClass b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      change cycleClass (tensorClass A * tensorClass B) =
        cycleClass (tensorClass A) * cycleClass (tensorClass B)
      rw [← classOf_coeff A, ← classOf_coeff B, ← classOf_product]
      rw [cycleClass_classOf, cycleClass_classOf, cycleClass_classOf, ← classOf_product]
      rfl

@[simp] theorem cycleClass_one : cycleClass (1 : TensorClass K) = 1 := by
  change cycleClass (classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))) = _
  rw [cycleClass_classOf]
  rfl

theorem tensorClass_symmetrize_eq (A : FiniteTensor K) :
    tensorClass (symmetrize A) = tensorClass A * cycleClass (tensorClass A) *
      cycleClass (cycleClass (tensorClass A)) := rfl

theorem symmetrize_cycleClass_fixed (A : FiniteTensor K) :
    cycleClass (tensorClass (symmetrize A)) = tensorClass (symmetrize A) := by
  rw [tensorClass_symmetrize_eq, cycleClass_mul, cycleClass_mul, cycleClass_three]
  ring

theorem symmetrize_class_eq_cube {A : FiniteTensor K}
    (h : cycleClass (tensorClass A) = tensorClass A) :
    tensorClass (symmetrize A) = tensorClass A ^ 3 := by
  rw [tensorClass_symmetrize_eq, h, h]
  ring

theorem Isomorphic.cycleClass_fixed {A : FiniteTensor K}
    (h : Isomorphic A (permute .yzx A)) : cycleClass (tensorClass A) = tensorClass A :=
  h.tensorClass_eq.symm

theorem ClassDegenerates.cycle {a b : TensorClass K} (h : ClassDegenerates a b) :
    ClassDegenerates (cycleClass a) (cycleClass b) := by
  obtain ⟨A, B, hA, hB, hd⟩ := h
  refine ⟨permute .yzx A, permute .yzx B, ?_, ?_, hd.cyclic⟩
  · rw [← cycleClass_tensorClass, hA]
  · rw [← cycleClass_tensorClass, hB]

end BlockIdentities.Square
