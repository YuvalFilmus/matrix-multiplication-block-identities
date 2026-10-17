/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Tensor.ConvolutionSplittings
public import Mathlib.Data.Fin.Rev

/-! Genuine coordinate-permutation isomorphisms of finite coefficient tensors. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [Field K]

/-- Precomposition by a coordinate equivalence is an invertible linear change. -/
def coordinateLinearEquiv {X Y : Type*} (e : X ≃ Y) :
    (Y → K) ≃ₗ[K] (X → K) where
  toFun f := fun x => f (e x)
  invFun f := fun y => f (e.symm y)
  left_inv f := by funext y; simp
  right_inv f := by funext x; simp
  map_add' f g := rfl
  map_smul' a f := rfl

/-- An exact pullback along three bijections is an actual tensor isomorphism. -/
theorem isomorphic_of_coordinate_equivalences (A B : FiniteTensor K)
    (ex : Fin B.nx ≃ Fin A.nx) (ey : Fin B.ny ≃ Fin A.ny)
    (ez : Fin B.nz ≃ Fin A.nz)
    (h : B.coeff = Tensor.pullback ex ey ez A.coeff) : Isomorphic A B := by
  classical
  refine ⟨coordinateLinearEquiv ex, coordinateLinearEquiv ey,
    coordinateLinearEquiv ez, ?_⟩
  rw [h, Tensor.pullback_eq_restrict]
  congr 1 <;> funext x i <;>
    simp [coordinateLinearEquiv, Pi.single_apply, eq_comm]

/-- Reversing only the intrinsic middle block's first leg gives the prescribed
(23)-oriented convolution tensor; the common leg of a shared sum is untouched. -/
theorem middleConvolution_isomorphic (r : ℕ+) :
    Isomorphic (middleConvolution (K := K) r)
      (permute .xzy (convolution r r)) := by
  let e := Fintype.equivFin (Fin (r : ℕ))
  let ex := e.symm.trans (Fin.revPerm.trans e)
  refine isomorphic_of_coordinate_equivalences
    (middleConvolution (K := K) r) (permute .xzy (convolution r r))
    ex (Equiv.refl _) (Equiv.refl _) ?_
  have hex (x : Fin (Fintype.card (Fin (r : ℕ)))) :
      e.symm (ex x) = (e.symm x).rev := by
    change e.symm (e ((e.symm x).rev)) = (e.symm x).rev
    exact e.symm_apply_apply _
  funext x y z
  change Fin (Fintype.card (Fin (r : ℕ))) at x z
  change Fin (Fintype.card (Fin ((r : ℕ) + (r : ℕ) - 1))) at y
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r r
  let ez := Fintype.equivFin (Fin ((r : ℕ) + (r : ℕ) - 1))
  change C (e.symm x) (e.symm z) (ez.symm y) =
    C (e.symm (ex x)).rev (e.symm z) (ez.symm y)
  rw [hex, Fin.rev_rev]

/-- Interchanging the two convolution inputs changes only their tensor legs. -/
theorem convolution_input_swap_isomorphic (r b : ℕ+) :
    Isomorphic (convolution (K := K) r b)
      (permute .yxz (convolution b r)) := by
  let ez : Fin ((b : ℕ) + (r : ℕ) - 1) ≃ Fin ((r : ℕ) + (b : ℕ) - 1) :=
    { toFun := fun z => ⟨z.val, by omega⟩
      invFun := fun z => ⟨z.val, by omega⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun z => by ext; rfl }
  let eZ := (Fintype.equivFin (Fin ((b : ℕ) + (r : ℕ) - 1))).symm.trans
    (ez.trans (Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))))
  refine isomorphic_of_coordinate_equivalences
    (convolution (K := K) r b) (permute .yxz (convolution b r))
    (Equiv.refl _) (Equiv.refl _) eZ ?_
  funext x y z
  change Fin (Fintype.card (Fin (r : ℕ))) at x
  change Fin (Fintype.card (Fin (b : ℕ))) at y
  change Fin (Fintype.card (Fin ((b : ℕ) + (r : ℕ) - 1))) at z
  have hz :
      (Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm (eZ z) =
      ez ((Fintype.equivFin (Fin ((b : ℕ) + (r : ℕ) - 1))).symm z) := by
    change (Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm
      ((Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1)))
        (ez ((Fintype.equivFin (Fin ((b : ℕ) + (r : ℕ) - 1))).symm z))) = _
    exact Equiv.symm_apply_apply _ _
  change
    (if ((Fintype.equivFin (Fin (b : ℕ))).symm y).val +
        ((Fintype.equivFin (Fin (r : ℕ))).symm x).val =
        ((Fintype.equivFin (Fin ((b : ℕ) + (r : ℕ) - 1))).symm z).val
      then (1 : K) else 0) =
    (if ((Fintype.equivFin (Fin (r : ℕ))).symm x).val +
        ((Fintype.equivFin (Fin (b : ℕ))).symm y).val =
        ((Fintype.equivFin (Fin ((r : ℕ) + (b : ℕ) - 1))).symm (eZ z)).val
      then (1 : K) else 0)
  have hval (w : Fin ((b : ℕ) + (r : ℕ) - 1)) : (ez w).val = w.val := rfl
  rw [hz, hval, Nat.add_comm]

/-- The manuscript's exact lower-boundary isomorphism as a provider theorem. -/
theorem convolution_boundary_isomorphic (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    Isomorphic
      (convolution (K := K) r ⟨(r : ℕ) - 1, by omega⟩)
      (permute .yxz (convolution ⟨(r : ℕ) - 1, by omega⟩ r)) :=
  convolution_input_swap_isomorphic r ⟨(r : ℕ) - 1, by omega⟩

end BlockIdentities.Square
