/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.ClassDegeneration

/-! Finite catalytic reuse: the auxiliary tensor is supplied only once. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring

variable {K : Type*} [Field K]

/-- Repeatedly apply one fixed conversion while keeping the same catalyst. -/
theorem catalytic_reuse {A B Z : TensorClass K} (a : ℕ)
    (h : ClassDegenerates ((a : TensorClass K) * A * Z) (B * Z)) (j : ℕ) :
    ClassDegenerates ((a : TensorClass K) ^ j * A ^ j * Z) (B ^ j * Z) := by
  induction j with
  | zero => simpa only [pow_zero, one_mul] using ClassDegenerates.refl Z
  | succ j ih =>
    have hfirst := (ClassDegenerates.refl ((a : TensorClass K) ^ j * A ^ j)).mul h
    have hsecond := (ClassDegenerates.refl B).mul ih
    have heq : ((a : TensorClass K) ^ j * A ^ j) *
        ((a : TensorClass K) * A * Z) =
        (a : TensorClass K) ^ (j + 1) * A ^ (j + 1) * Z := by ring
    have hmid : ((a : TensorClass K) ^ j * A ^ j) * (B * Z) =
        B * ((a : TensorClass K) ^ j * A ^ j * Z) := by ring
    have hout : B * (B ^ j * Z) = B ^ (j + 1) * Z := by ring
    rw [heq, hmid] at hfirst
    rw [hout] at hsecond
    exact hfirst.trans hsecond

/-- Supply the catalyst from R scalars once, then discard it at the end.
This finite statement does not assume or assert asymptotic cancellation. -/
theorem finite_catalytic_reuse {A B Z : TensorClass K} (a R : ℕ)
    (h : ClassDegenerates ((a : TensorClass K) * A * Z) (B * Z))
    (hZ : 1 ≤ Z) (hR : Z ≤ (R : TensorClass K)) (j : ℕ) :
    ClassDegenerates (((R : TensorClass K) * (a : TensorClass K) ^ j) * A ^ j)
      (B ^ j) := by
  have hsupply : ((a : TensorClass K) ^ j * A ^ j) * Z ≤
      ((R : TensorClass K) * (a : TensorClass K) ^ j) * A ^ j := by
    calc
      _ ≤ ((a : TensorClass K) ^ j * A ^ j) * (R : TensorClass K) :=
        mul_mono le_rfl hR
      _ = _ := by ring
  have hdiscard : B ^ j ≤ B ^ j * Z := by
    simpa only [mul_one] using (mul_mono (le_refl (B ^ j)) hZ)
  exact ((ClassDegenerates.of_le hsupply).trans (catalytic_reuse a h j)).trans
    (ClassDegenerates.of_le hdiscard)

/-- The same finite reuse with explicit degeneration witnesses for supplying
and recovering the catalyst. -/
theorem finite_catalytic_conversion {A B Z : TensorClass K} (a R : ℕ)
    (h : ClassDegenerates ((a : TensorClass K) * A * Z) (B * Z))
    (hZ : ClassDegenerates Z 1) (hR : ClassDegenerates (R : TensorClass K) Z)
    (j : ℕ) :
    ClassDegenerates (((R : TensorClass K) * (a : TensorClass K) ^ j) * A ^ j)
      (B ^ j) := by
  have hs := (ClassDegenerates.refl ((a : TensorClass K) ^ j * A ^ j)).mul hR
  have hd := (ClassDegenerates.refl (B ^ j)).mul hZ
  have heq : ((a : TensorClass K) ^ j * A ^ j) * R =
      ((R : TensorClass K) * (a : TensorClass K) ^ j) * A ^ j := by ring
  rw [heq] at hs
  simp only [mul_one] at hd
  exact (hs.trans (catalytic_reuse a h j)).trans hd

end BlockIdentities.Square
