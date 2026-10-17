/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.CyclicClasses

/-! Swapping the last two tensor legs on actual finite tensor classes and
polynomial local-map degenerations. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Interchange the last two coordinate groups of a coefficient tensor. -/
def swapLast {R X Y Z : Type*} (T : Tensor R X Y Z) : Tensor R X Z Y :=
  fun x z y => T x y z

/-- All three local maps move with their tensor legs. -/
theorem swapLast_restrict {R X Y Z U V W : Type*} [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z]
    (Lx : U → X → R) (Ly : V → Y → R) (Lz : W → Z → R)
    (T : Tensor R X Y Z) :
    swapLast (Tensor.restrict Lx Ly Lz T) =
      Tensor.restrict Lx Lz Ly (swapLast T) := by
  funext x z y
  simp only [swapLast, Tensor.restrict]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A restriction remains a restriction after interchanging the side legs. -/
theorem permute_xzy_mono {A B : FiniteTensor K} (h : A ≤ B) :
    permute .xzy A ≤ permute .xzy B := by
  obtain ⟨Lx, Ly, Lz, h⟩ := h
  refine ⟨Lx, Lz, Ly, ?_⟩
  change swapLast A.coeff = Tensor.restrict Lx Lz Ly (swapLast B.coeff)
  rw [h]
  exact swapLast_restrict Lx Ly Lz B.coeff

/-- The actual last-two-leg swap descends through mutual linear restriction. -/
def swapClass : TensorClass K → TensorClass K :=
  Quotient.map (permute .xzy) (by
    intro A B h
    exact ⟨permute_xzy_mono h.1, permute_xzy_mono h.2⟩)

@[simp] theorem swapClass_tensorClass (A : FiniteTensor K) :
    swapClass (tensorClass A) = tensorClass (permute .xzy A) := rfl

theorem swapClass_classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : swapClass (classOf T) = classOf (swapLast T) := by
  change tensorClass (permute .xzy (FiniteTensor.ofTensor T)) = _
  rw [← classOf_coeff]
  exact classOf_reindex (swapLast T) (Fintype.equivFin X).symm
    (Fintype.equivFin Z).symm (Fintype.equivFin Y).symm

@[simp] theorem swapClass_two (a : TensorClass K) : swapClass (swapClass a) = a := by
  induction a using Quotient.inductionOn with
  | h A => rfl

@[simp] theorem swapClass_mul (a b : TensorClass K) :
    swapClass (a * b) = swapClass a * swapClass b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      change swapClass (tensorClass A * tensorClass B) =
        swapClass (tensorClass A) * swapClass (tensorClass B)
      rw [← classOf_coeff A, ← classOf_coeff B, ← classOf_product]
      rw [swapClass_classOf, swapClass_classOf, swapClass_classOf, ← classOf_product]
      rfl

@[simp] theorem swapClass_one : swapClass (1 : TensorClass K) = 1 := by
  change swapClass (classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))) = _
  rw [swapClass_classOf]
  rfl

@[simp] theorem swapClass_pow (a : TensorClass K) (n : ℕ) :
    swapClass (a ^ n) = swapClass a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, swapClass_mul, ih]

/-- The transposition conjugates a three-cycle to its inverse. -/
theorem swapClass_cycleClass (a : TensorClass K) :
    swapClass (cycleClass a) = cycleClass (cycleClass (swapClass a)) := by
  induction a using Quotient.inductionOn with
  | h A => rfl

/-- Explicitly swap polynomial local maps, their degree bounds, and all target
coordinates while retaining the common leading order. -/
def polynomialDegeneration_swapLast
    {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {k lx ly lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T S k lx ly lz) :
    Tensor.PolynomialRestrictionDegeneration (swapLast T) (swapLast S) k lx lz ly where
  leftMap := L.leftMap
  middleMap := L.rightMap
  rightMap := L.middleMap
  left_degree := L.left_degree
  middle_degree := L.right_degree
  right_degree := L.middle_degree
  vanishes := by
    intro x z y j hj
    have h := congrFun (congrFun (congrFun
      (swapLast_restrict L.leftMap L.middleMap L.rightMap
        (fun x y z => Polynomial.C (T x y z))) x) z) y
    exact (congrArg (fun P : Polynomial K => P.coeff j) h).symm.trans
      (L.vanishes x y z j hj)
  leading := by
    intro x z y
    have h := congrFun (congrFun (congrFun
      (swapLast_restrict L.leftMap L.middleMap L.rightMap
        (fun x y z => Polynomial.C (T x y z))) x) z) y
    exact (congrArg (fun P : Polynomial K => P.coeff k) h).symm.trans
      (L.leading x y z)

theorem Degenerates.swap {A B : FiniteTensor K} (h : Degenerates A B) :
    Degenerates (permute .xzy A) (permute .xzy B) := by
  obtain ⟨k, lx, ly, lz, ⟨L⟩⟩ := h
  exact ⟨k, lx, lz, ly, ⟨polynomialDegeneration_swapLast L⟩⟩

theorem ClassDegenerates.swap {a b : TensorClass K} (h : ClassDegenerates a b) :
    ClassDegenerates (swapClass a) (swapClass b) := by
  obtain ⟨A, B, hA, hB, hd⟩ := h
  refine ⟨permute .xzy A, permute .xzy B, ?_, ?_, hd.swap⟩
  · rw [← swapClass_tensorClass, hA]
  · rw [← swapClass_tensorClass, hB]

end BlockIdentities.Square
