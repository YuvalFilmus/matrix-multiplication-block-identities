/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.Ring

/-! Coefficient jets at zero for the two independent groups of circuit inputs.
The mixed derivative uses distinct Sum legs, so no factorial or characteristic
assumption enters the bilinear coefficient calculus. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

variable {F X Y : Type*} [Field F]

/-- The constant coefficient, evaluated by the zero assignment. -/
def zeroJet (f : MvPolynomial (X ⊕ Y) F) : F := MvPolynomial.eval (fun _ => 0) f

/-- The coefficient of one variable from the left group. -/
def leftJet (f : MvPolynomial (X ⊕ Y) F) (x : X) : F :=
  MvPolynomial.eval (fun _ => 0) (MvPolynomial.pderiv (Sum.inl x) f)

/-- The coefficient of one variable from the right group. -/
def rightJet (f : MvPolynomial (X ⊕ Y) F) (y : Y) : F :=
  MvPolynomial.eval (fun _ => 0) (MvPolynomial.pderiv (Sum.inr y) f)

/-- The coefficient with one occurrence from each independent input group. -/
def mixedJet (f : MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) : F :=
  MvPolynomial.eval (fun _ => 0)
    (MvPolynomial.pderiv (Sum.inr y) (MvPolynomial.pderiv (Sum.inl x) f))

@[simp] theorem zeroJet_add (f g : MvPolynomial (X ⊕ Y) F) :
    zeroJet (f + g) = zeroJet f + zeroJet g := by simp [zeroJet]

@[simp] theorem zeroJet_sub (f g : MvPolynomial (X ⊕ Y) F) :
    zeroJet (f - g) = zeroJet f - zeroJet g := by simp [zeroJet]

@[simp] theorem zeroJet_mul (f g : MvPolynomial (X ⊕ Y) F) :
    zeroJet (f * g) = zeroJet f * zeroJet g := by simp [zeroJet]

@[simp] theorem leftJet_add (f g : MvPolynomial (X ⊕ Y) F) (x : X) :
    leftJet (f + g) x = leftJet f x + leftJet g x := by simp [leftJet]

@[simp] theorem leftJet_sub (f g : MvPolynomial (X ⊕ Y) F) (x : X) :
    leftJet (f - g) x = leftJet f x - leftJet g x := by simp [leftJet]

@[simp] theorem rightJet_add (f g : MvPolynomial (X ⊕ Y) F) (y : Y) :
    rightJet (f + g) y = rightJet f y + rightJet g y := by simp [rightJet]

@[simp] theorem rightJet_sub (f g : MvPolynomial (X ⊕ Y) F) (y : Y) :
    rightJet (f - g) y = rightJet f y - rightJet g y := by simp [rightJet]

@[simp] theorem mixedJet_add (f g : MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) :
    mixedJet (f + g) x y = mixedJet f x y + mixedJet g x y := by simp [mixedJet]

@[simp] theorem mixedJet_sub (f g : MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) :
    mixedJet (f - g) x y = mixedJet f x y - mixedJet g x y := by simp [mixedJet]

/-- First-order Leibniz rule for the left leg. -/
theorem leftJet_mul (f g : MvPolynomial (X ⊕ Y) F) (x : X) :
    leftJet (f * g) x = leftJet f x * zeroJet g + zeroJet f * leftJet g x := by
  simp [leftJet, zeroJet]
  ring

/-- First-order Leibniz rule for the right leg. -/
theorem rightJet_mul (f g : MvPolynomial (X ⊕ Y) F) (y : Y) :
    rightJet (f * g) y = rightJet f y * zeroJet g + zeroJet f * rightJet g y := by
  simp [rightJet, zeroJet]
  ring

/-- The four bidegree contributions at a multiplication gate. -/
theorem mixedJet_mul (f g : MvPolynomial (X ⊕ Y) F) (x : X) (y : Y) :
    mixedJet (f * g) x y =
      zeroJet f * mixedJet g x y + mixedJet f x y * zeroJet g +
      leftJet f x * rightJet g y + rightJet f y * leftJet g x := by
  simp only [mixedJet, leftJet, rightJet, zeroJet, MvPolynomial.pderiv_mul,
    map_add, map_mul]
  ring

@[simp] theorem zeroJet_C (c : F) : zeroJet (MvPolynomial.C c : MvPolynomial (X ⊕ Y) F) = c := by
  simp [zeroJet]

@[simp] theorem leftJet_C (c : F) (x : X) :
    leftJet (MvPolynomial.C c : MvPolynomial (X ⊕ Y) F) x = 0 := by
  simp [leftJet]

@[simp] theorem rightJet_C (c : F) (y : Y) :
    rightJet (MvPolynomial.C c : MvPolynomial (X ⊕ Y) F) y = 0 := by
  simp [rightJet]

@[simp] theorem mixedJet_C (c : F) (x : X) (y : Y) :
    mixedJet (MvPolynomial.C c) x y = 0 := by
  simp [mixedJet]

@[simp] theorem zeroJet_X (i : X ⊕ Y) :
    zeroJet (MvPolynomial.X i : MvPolynomial (X ⊕ Y) F) = 0 := by simp [zeroJet]

@[simp] theorem leftJet_X_right (x : X) (y : Y) :
    leftJet (MvPolynomial.X (Sum.inr y) : MvPolynomial (X ⊕ Y) F) x = 0 := by
  classical
  simp [leftJet]

@[simp] theorem rightJet_X_left (x : X) (y : Y) :
    rightJet (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Y) F) y = 0 := by
  classical
  simp [rightJet]

@[simp] theorem leftJet_X_left [DecidableEq X] (x x' : X) :
    leftJet (MvPolynomial.X (Sum.inl x') : MvPolynomial (X ⊕ Y) F) x =
      if x = x' then 1 else 0 := by
  classical
  simp [leftJet, Pi.single_apply, eq_comm]

@[simp] theorem rightJet_X_right [DecidableEq Y] (y y' : Y) :
    rightJet (MvPolynomial.X (Sum.inr y') : MvPolynomial (X ⊕ Y) F) y =
      if y = y' then 1 else 0 := by
  classical
  simp [rightJet, Pi.single_apply, eq_comm]

@[simp] theorem mixedJet_X (i : X ⊕ Y) (x : X) (y : Y) :
    mixedJet (MvPolynomial.X i : MvPolynomial (X ⊕ Y) F) x y = 0 := by
  classical
  by_cases h : i = Sum.inl x
  · subst i
    simp [mixedJet]
  · simp [mixedJet, MvPolynomial.pderiv_X_of_ne h]

/-- Exact mixed coefficients of a left input times a right input. -/
@[simp] theorem mixedJet_X_left_mul_X_right [DecidableEq X] [DecidableEq Y]
    (x x' : X) (y y' : Y) :
    mixedJet ((MvPolynomial.X (Sum.inl x') : MvPolynomial (X ⊕ Y) F) *
      MvPolynomial.X (Sum.inr y')) x y =
        (if x = x' then 1 else 0) * (if y = y' then 1 else 0) := by
  rw [mixedJet_mul]
  simp

end BlockIdentities.Arithmetic
