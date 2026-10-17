/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.DegenerationProduct

/-! Nonnegative integral coordinate weights give actual polynomial maps. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open scoped BigOperators
variable {K X Y Z : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

/-- The literal weight-k part of a coefficient tensor. -/
def weightPart (T : Tensor K X Y Z) (wx : X → ℕ) (wy : Y → ℕ) (wz : Z → ℕ)
    (k : ℕ) : Tensor K X Y Z :=
  fun x y z => if wx x + wy y + wz z = k then T x y z else 0

def diagonalWeightMap [DecidableEq X] (w : X → ℕ) (x i : X) : Polynomial K :=
  if i = x then Polynomial.X ^ w x else 0

theorem diagonalWeight_base [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) (wx : X → ℕ) (wy : Y → ℕ) (wz : Z → ℕ)
    (x : X) (y : Y) (z : Z) :
    Tensor.restrict (diagonalWeightMap wx) (diagonalWeightMap wy) (diagonalWeightMap wz)
      (fun i j k => Polynomial.C (T i j k)) x y z =
      Polynomial.X ^ (wx x + wy y + wz z) * Polynomial.C (T x y z) := by
  simp [Tensor.restrict, diagonalWeightMap, pow_add] <;> ring

/-- The supported minimum weight is the leading coefficient of explicit
polynomial diagonal maps. Coordinate bounds are genuine finite map degrees. -/
def weightPartDegeneration [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) (wx : X → ℕ) (wy : Y → ℕ) (wz : Z → ℕ)
    (k Lx Ly Lz : ℕ)
    (hx : ∀ x, wx x ≤ Lx) (hy : ∀ y, wy y ≤ Ly) (hz : ∀ z, wz z ≤ Lz)
    (hmin : ∀ x y z, T x y z ≠ 0 → k ≤ wx x + wy y + wz z) :
    Tensor.PolynomialRestrictionDegeneration T (weightPart T wx wy wz k) k Lx Ly Lz where
  leftMap := diagonalWeightMap wx
  middleMap := diagonalWeightMap wy
  rightMap := diagonalWeightMap wz
  left_degree := by
    intro x i
    apply Polynomial.degree_le_of_natDegree_le
    simp only [diagonalWeightMap]
    split_ifs <;> simp [hx x]
  middle_degree := by
    intro y i
    apply Polynomial.degree_le_of_natDegree_le
    simp only [diagonalWeightMap]
    split_ifs <;> simp [hy y]
  right_degree := by
    intro z i
    apply Polynomial.degree_le_of_natDegree_le
    simp only [diagonalWeightMap]
    split_ifs <;> simp [hz z]
  vanishes := by
    intro x y z j hj
    rw [diagonalWeight_base, Polynomial.coeff_X_pow_mul']
    by_cases ht : T x y z = 0
    · simp [ht]
    · simp only [Nat.not_le_of_lt (lt_of_lt_of_le hj (hmin x y z ht)), ite_false]
  leading := by
    intro x y z
    rw [diagonalWeight_base, Polynomial.coeff_X_pow_mul']
    by_cases ht : T x y z = 0
    · simp [ht, weightPart]
    · have hm := hmin x y z ht
      by_cases he : wx x + wy y + wz z = k
      · simp [he, weightPart]
      · have hk : k < wx x + wy y + wz z := lt_of_le_of_ne hm (Ne.symm he)
        simp [Nat.not_le_of_lt hk, weightPart, he]

end BlockIdentities.Square
