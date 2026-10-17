/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ValueMatrices
public import BlockIdentities.Tensor.ValueSymmetries
public import BlockIdentities.Tensor.IsomorphismClasses
public import BlockIdentities.Frozen.convolution_boundary_isomorphism_v2
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic

/-! Nonzero convolution tensors and their exact lower-boundary values. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.Foundation
variable {K : Type*} [Field K]

/-- Positive convolution dimensions give a nonzero formal coefficient tensor. -/
theorem nonzero_convolution (r b : ℕ+) : Nonzero (convolution (K := K) r b) :=
  nonzero_ofTensor
    (OAI.MatrixMultiplication.AuxiliarySeparation.convolution_nonzero r.property b.property)

def nonzeroConvolution (r b : ℕ+) : NonzeroTensor K :=
  ⟨convolution r b, nonzero_convolution r b⟩

/-- The boundary isomorphism and value's actual permutation invariance transport
normalized values without identifying shared first-leg maps. -/
theorem normalizedValue_convolution_boundary [IsAlgClosed K]
    (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    normalizedValueAtOmega (nonzeroConvolution (K := K) r ⟨(r : ℕ) - 1, by omega⟩) =
      normalizedValueAtOmega (nonzeroConvolution (K := K) ⟨(r : ℕ) - 1, by omega⟩ r) := by
  let ρ : Set.Icc (2 : ℝ) 3 :=
    ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
  let A := nonzeroConvolution (K := K) r ⟨(r : ℕ) - 1, by omega⟩
  let B := nonzeroConvolution (K := K) ⟨(r : ℕ) - 1, by omega⟩ r
  have he := value_eq_of_tensorClass_eq ρ A (B.permute .yxz)
    (convolution_boundary_isomorphism (K := K) r hr).tensorClass_eq
  have hp := value_permute ρ B .yxz
  have hv : valueAtOmega A = valueAtOmega B := he.trans hp
  change valueAtOmega A ^ (3 / Arithmetic.formalOmega K) =
    valueAtOmega B ^ (3 / Arithmetic.formalOmega K)
  rw [hv]

/-- Evaluate one canonical product coordinate layer before exposing another. -/
private theorem product_coeff_at_pair (A B : FiniteTensor K)
    (x : Fin A.nx) (y : Fin A.ny) (z : Fin A.nz)
    (u : Fin B.nx) (v : Fin B.ny) (w : Fin B.nz) :
    (product A B).coeff
      (Fintype.equivFin _ (x, u)) (Fintype.equivFin _ (y, v))
      (Fintype.equivFin _ (z, w)) = A.coeff x y z * B.coeff u v w := by
  change A.coeff ((Fintype.equivFin _).symm (Fintype.equivFin _ (x, u))).1
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (y, v))).1
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (z, w))).1 *
    B.coeff ((Fintype.equivFin _).symm (Fintype.equivFin _ (x, u))).2
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (y, v))).2
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (z, w))).2 = _
  simp only [Equiv.symm_apply_apply]

private theorem convolution_two_one_coeff (x z : Fin 2) (u : Fin 1) :
    (convolution (K := K) 2 1).coeff
      (Fintype.equivFin _ x) (Fintype.equivFin _ u) (Fintype.equivFin _ z) =
      if x = z then 1 else 0 := by
  change (if ((Fintype.equivFin _).symm (Fintype.equivFin _ x)).val +
      ((Fintype.equivFin _).symm (Fintype.equivFin _ u)).val =
      ((Fintype.equivFin _).symm (Fintype.equivFin _ z)).val then (1 : K) else 0) = _
  simp only [Equiv.symm_apply_apply, Fin.eq_zero u, Fin.val_zero, Nat.add_zero, Fin.ext_iff]

private theorem terminal_delta_product (x y z : Fin 2 × Fin 2) :
    matrixMultiplicationTensor (K := K) 2 2 2 x y z =
      ((if x.1 = z.2 then 1 else 0) * (if z.1 = y.2 then 1 else 0)) *
        (if y.1 = x.2 then 1 else 0) := by
  by_cases h₁ : x.1 = z.2 <;> by_cases h₂ : z.1 = y.2 <;>
    by_cases h₃ : y.1 = x.2 <;>
      simp [matrixMultiplicationTensor, h₁, h₂, h₃, eq_comm]

/-- Actual terminal coordinate maps; all three nontrivial index spaces have size2. -/
theorem convolution_two_one_terminal_isomorphic :
    Isomorphic (symmetrize (convolution (K := K) 2 1)) (square 2) := by
  let C := convolution (K := K) 2 1
  let P := product C (permute .yzx C)
  let eR := Fintype.equivFin (Fin 2)
  let eU := Fintype.equivFin (Fin 1)
  let eM := Fintype.equivFin (Fin 2 × Fin 2)
  let ePX := Fintype.equivFin (Fin C.nx × Fin C.ny)
  let ePY := Fintype.equivFin (Fin C.ny × Fin C.nz)
  let ePZ := Fintype.equivFin (Fin C.nz × Fin C.nx)
  let eFX := Fintype.equivFin (Fin P.nx × Fin C.nz)
  let eFY := Fintype.equivFin (Fin P.ny × Fin C.nx)
  let eFZ := Fintype.equivFin (Fin P.nz × Fin C.ny)
  let a : (Fin 2 × Fin 2) ≃ ((Fin 2 × Fin 1) × Fin 2) :=
    { toFun := fun x => ((x.1, 0), x.2)
      invFun := fun x => (x.1.1, x.2)
      left_inv := by intro x; rfl
      right_inv := by rintro ⟨⟨i, u⟩, j⟩; have hu : u = 0 := Subsingleton.elim _ _; subst u; rfl }
  let b : (Fin 2 × Fin 2) ≃ ((Fin 1 × Fin 2) × Fin 2) :=
    { toFun := fun y => ((0, y.2), y.1)
      invFun := fun y => (y.2, y.1.2)
      left_inv := by intro y; rfl
      right_inv := by rintro ⟨⟨u, k⟩, j⟩; have hu : u = 0 := Subsingleton.elim _ _; subst u; rfl }
  let c : (Fin 2 × Fin 2) ≃ ((Fin 2 × Fin 2) × Fin 1) :=
    { toFun := fun z => ((z.2, z.1), 0)
      invFun := fun z => (z.1.2, z.1.1)
      left_inv := by intro z; rfl
      right_inv := by rintro ⟨⟨i, k⟩, u⟩; have hu : u = 0 := Subsingleton.elim _ _; subst u; rfl }
  let ex := (eM.symm.trans a).trans
    ((Equiv.prodCongr ((Equiv.prodCongr eR eU).trans ePX) eR).trans eFX)
  let ey := (eM.symm.trans b).trans
    ((Equiv.prodCongr ((Equiv.prodCongr eU eR).trans ePY) eR).trans eFY)
  let ez := (eM.symm.trans c).trans
    ((Equiv.prodCongr ((Equiv.prodCongr eR eR).trans ePZ) eU).trans eFZ)
  apply isomorphic_of_coordinate_equivalences (symmetrize C) (square 2) ex ey ez
  funext x y z
  change Fin (Fintype.card (Fin 2 × Fin 2)) at x y z
  change OAI.MatrixMultiplication.AuxiliarySeparation.matrixMultiplicationTensor 2 2 2
    (eM.symm x) (eM.symm y) (eM.symm z) = _
  change matrixMultiplicationTensor 2 2 2 (eM.symm x) (eM.symm y) (eM.symm z) =
    (product P (permute .zxy C)).coeff
      (eFX (ePX (eR (eM.symm x).1, eU 0), eR (eM.symm x).2))
      (eFY (ePY (eU 0, eR (eM.symm y).2), eR (eM.symm y).1))
      (eFZ (ePZ (eR (eM.symm z).2, eR (eM.symm z).1), eU 0))
  erw [product_coeff_at_pair]
  change matrixMultiplicationTensor 2 2 2 (eM.symm x) (eM.symm y) (eM.symm z) =
    (product C (permute .yzx C)).coeff
      (ePX (eR (eM.symm x).1, eU 0))
      (ePY (eU 0, eR (eM.symm y).2))
      (ePZ (eR (eM.symm z).2, eR (eM.symm z).1)) *
      C.coeff (eR (eM.symm y).1) (eU 0) (eR (eM.symm x).2)
  erw [product_coeff_at_pair]
  change matrixMultiplicationTensor 2 2 2 (eM.symm x) (eM.symm y) (eM.symm z) =
    (C.coeff (eR (eM.symm x).1) (eU 0) (eR (eM.symm z).2) *
      C.coeff (eR (eM.symm z).1) (eU 0) (eR (eM.symm y).2)) *
      C.coeff (eR (eM.symm y).1) (eU 0) (eR (eM.symm x).2)
  erw [convolution_two_one_coeff, convolution_two_one_coeff, convolution_two_one_coeff]
  exact terminal_delta_product (eM.symm x) (eM.symm y) (eM.symm z)

/-- The actual terminal's normalized value is exactly2. -/
theorem normalizedValue_convolution_two_one [IsAlgClosed K] :
    normalizedValueAtOmega (nonzeroConvolution (K := K) 2 1) = 2 :=
  normalizedValueAtOmega_terminal _ 2 (by decide) convolution_two_one_terminal_isomorphic

end BlockIdentities.Square
