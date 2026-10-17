/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ClassDegeneration
public import BlockIdentities.Tensor.ClassIdentities
public import Mathlib.Algebra.BigOperators.Fin

/-! Genuine finite tensor products on dependent coordinate families. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

def familyProduct {ι : Type*} [Fintype ι] {X Y Z : ι → Type*}
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor K (∀ i, X i) (∀ i, Y i) (∀ i, Z i) :=
  fun x y z => ∏ i, T i (x i) (y i) (z i)

private def splitDependent (n : ℕ) (X : Fin (n + 1) → Type*) :
    (X 0 × (∀ j : Fin n, X j.succ)) ≃ (∀ i, X i) where
  toFun p := Fin.cases p.1 p.2
  invFun f := (f 0, fun j => f j.succ)
  left_inv p := by cases p; rfl
  right_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i

private def emptyDependent (X : Fin 0 → Type*) : (∀ i, X i) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ i := Fin.elim0 i
  left_inv f := by funext i; exact Fin.elim0 i
  right_inv u := by cases u; rfl

theorem classOf_familyProduct (n : ℕ) {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    classOf (familyProduct T) = ∏ i, classOf (T i) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    change classOf (familyProduct T) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
    apply classOf_eq_of_reindex (emptyDependent X) (emptyDependent Y) (emptyDependent Z)
    funext x y z
    simp [Tensor.pullback, familyProduct]
  | succ n ih =>
    have heq : Tensor.pullback (splitDependent n X) (splitDependent n Y) (splitDependent n Z)
        (familyProduct T) = Tensor.product (T 0) (familyProduct (fun j : Fin n => T j.succ)) := by
      funext x y z
      simp [Tensor.pullback, familyProduct, splitDependent, Tensor.product, Fin.prod_univ_succ]
    calc
      classOf (familyProduct T) =
          classOf (Tensor.product (T 0) (familyProduct (fun j : Fin n => T j.succ))) :=
        (classOf_eq_of_reindex _ _ _ heq).symm
      _ = classOf (T 0) * classOf (familyProduct (fun j : Fin n => T j.succ)) :=
        classOf_product _ _
      _ = ∏ i, classOf (T i) := by rw [ih, Fin.prod_univ_succ]

theorem classOf_tensorPower {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (n : ℕ) : classOf (Tensor.power T n) = classOf T ^ n := by
  have h := classOf_familyProduct n (fun _ => T)
  change classOf (familyProduct (fun _ : Fin n => T)) = classOf T ^ n
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem ClassDegenerates.prod {ι : Type*} (s : Finset ι)
    {a b : ι → TensorClass K} (h : ∀ i ∈ s, ClassDegenerates (a i) (b i)) :
    ClassDegenerates (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using ClassDegenerates.refl (1 : TensorClass K)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end BlockIdentities.Square
