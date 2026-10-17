/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ConvolutionSharedIdentities
public import BlockIdentities.Rectangular.Frozen.convolution_general_tripling

/-! General positive-length shared-leg convolution identity. The middle first
coordinate is reversed only inside its actual individual block map. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

/-- Actual first-coordinate involution identifying the middle intrinsic block
with the side-swapped convolution, at arbitrary positive lengths. -/
theorem general_middle_convolution_class (r s : ℕ+) :
    classOf (fun (x : Fin (r : ℕ)) z y =>
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s x.rev y z) =
      tensorClass (permute .xzy (convolution (K := K) r s)) := by
  rw [← swapClass_tensorClass]
  change classOf (fun (x : Fin (r : ℕ)) z y =>
    OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s x.rev y z) =
    swapClass (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s))
  rw [swapClass_classOf]
  apply classOf_eq_of_reindex Fin.revPerm (Equiv.refl _) (Equiv.refl _)
  rfl

/-- Both outer blocks are C(r,s); the middle block has its exact .xzy orientation.
The common first leg is retained through the three-sector source degeneration. -/
def generalTriplingSharedIdentity (r s : ℕ+) :
    SharedLegIdentity
      (convolution (K := K) r ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
        show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
        have hr : 0 < (r : ℕ) := r.property
        have hs : 0 < (s : ℕ) := s.property
        omega⟩)
      (fun _ : Fin 3 => convolution r s) scalarShape (fun _ => scalarShape) := by
  classical
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s
  let b : ℕ+ := ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
    show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
    have hr : 0 < (r : ℕ) := r.property
    have hs : 0 < (s : ℕ) := s.property
    omega⟩
  apply sharedFirstThreeIdentity C (fun (x : Fin (r : ℕ)) z y => C x.rev y z) C
    (convolution r b) (fun _ : Fin 3 => convolution r s)
    scalarShape (fun _ => scalarShape) .xyz triplingOutputPermutation
  · have hp : Degenerates (product (convolution (K := K) r b) scalarShape.tensor)
        (convolution r b) := by
      apply (classDegenerates_tensorClass_iff _ _).mp
      rw [tensorClass_product_scalarShape]
      exact ClassDegenerates.refl _
    exact hp.trans (BlockIdentities.Rectangular.convolution_general_tripling r s)
  · rw [tensorClass_permute_product_scalarShape]
    simpa [triplingOutputPermutation, permute, convolution, C, classOf] using
      (ClassDegenerates.refl (classOf C))
  · rw [tensorClass_permute_product_scalarShape]
    change ClassDegenerates (classOf (fun (x : Fin (r : ℕ)) z y => C x.rev y z))
      (tensorClass (permute .xzy (convolution r s)))
    rw [general_middle_convolution_class r s]
    exact ClassDegenerates.refl _
  · rw [tensorClass_permute_product_scalarShape]
    simpa [triplingOutputPermutation, permute, convolution, C, classOf] using
      (ClassDegenerates.refl (classOf C))

end BlockIdentities.Square
