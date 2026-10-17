/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.CyclicClasses
public import BlockIdentities.Tensor.ValueBounds

/-! Literal tensor powers, cyclic symmetrization, and their nonzero carriers. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

@[simp] theorem cycleClass_pow (a : TensorClass K) (k : ℕ) :
    cycleClass (a ^ k) = cycleClass a ^ k := by
  induction k with
  | zero => simp only [pow_zero, cycleClass_one]
  | succ k ih => rw [pow_succ, cycleClass_mul, ih, pow_succ]

theorem symmetrize_power_class (A : FiniteTensor K) (k : ℕ) :
    tensorClass (symmetrize (power A k)) = tensorClass (symmetrize A) ^ k := by
  simp only [tensorClass_symmetrize_eq, tensorClass_power_eq, cycleClass_pow, mul_pow]

theorem nonzero_power {A : FiniteTensor K} (hA : Nonzero A) (k : ℕ) :
    Nonzero (power A k) := by
  classical
  obtain ⟨x, y, z, hxyz⟩ := (nonzero_iff A).1 hA
  apply nonzero_ofTensor
  intro hzero
  have hv := congrFun (congrFun (congrFun hzero (fun _ => x)) (fun _ => y)) (fun _ => z)
  have hp : A.coeff x y z ^ k = 0 := by
    simpa only [Tensor.power, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Pi.zero_apply] using hv
  exact (pow_ne_zero k hxyz) hp

def NonzeroTensor.power (A : NonzeroTensor K) (k : ℕ) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.power A.val k, nonzero_power A.property k⟩

def NonzeroTensor.symmetrize (A : NonzeroTensor K) : NonzeroTensor K :=
  ⟨BlockIdentities.Square.symmetrize A.val, nonzero_symmetrize A.property⟩

end BlockIdentities.Square
