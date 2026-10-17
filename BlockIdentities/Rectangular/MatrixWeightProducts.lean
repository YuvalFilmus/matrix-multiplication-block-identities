/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedWeights

/-! Literal componentwise matrix shapes and their ordered weights. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square

def MatrixShape.product (D E : MatrixShape) : MatrixShape :=
  ⟨D.a * E.a, D.b * E.b, D.c * E.c,
    Nat.mul_pos D.a_pos E.a_pos, Nat.mul_pos D.b_pos E.b_pos,
    Nat.mul_pos D.c_pos E.c_pos⟩

def MatrixShape.power (D : MatrixShape) (n : ℕ) : MatrixShape :=
  ⟨D.a ^ n, D.b ^ n, D.c ^ n,
    pow_pos D.a_pos n, pow_pos D.b_pos n, pow_pos D.c_pos n⟩

end BlockIdentities.Square
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
variable {F : Type*} [Field F]

theorem matrixWeight_product (S : InteriorSupport F) (D E : MatrixShape) :
    matrixWeight S (D.product E) = matrixWeight S D * matrixWeight S E := by
  have ha : 0 ≤ (D.a : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ (D.b : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (D.c : ℝ) := Nat.cast_nonneg _
  simp only [matrixWeight, MatrixShape.product, Nat.cast_mul,
    Real.mul_rpow ha (Nat.cast_nonneg _), Real.mul_rpow hb (Nat.cast_nonneg _),
    Real.mul_rpow hc (Nat.cast_nonneg _)]
  ring

theorem matrixWeight_power (S : InteriorSupport F) (D : MatrixShape) (n : ℕ) :
    matrixWeight S (D.power n) = matrixWeight S D ^ n := by
  simp only [matrixWeight, MatrixShape.power, Nat.cast_pow,
    Real.rpow_pow_comm (Nat.cast_nonneg D.a),
    Real.rpow_pow_comm (Nat.cast_nonneg D.b),
    Real.rpow_pow_comm (Nat.cast_nonneg D.c), mul_pow]

end BlockIdentities.Rectangular
