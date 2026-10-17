/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.SharedSumIdentity
public import BlockIdentities.Tensor.PermutationClasses
public import BlockIdentities.Tensor.IsomorphismClasses
public import BlockIdentities.Frozen.convolution_neighbor_degeneration_v2
public import BlockIdentities.Frozen.convolution_tripling_degeneration_v2
public import BlockIdentities.Frozen.tripling_middle_isomorphism_v2

/-! The actual convolution constructions instantiate shared-leg identities. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem tensorClass_product_scalarShape (A : FiniteTensor K) :
    tensorClass (product A scalarShape.tensor) = tensorClass A := by
  rw [tensorClass_product_eq]
  change tensorClass A * matrixClass 1 = tensorClass A
  rw [matrixClass_one, mul_one]

theorem tensorClass_permute_product_scalarShape (π : LegPermutation) (A : FiniteTensor K) :
    tensorClass (permute π (product A scalarShape.tensor)) = tensorClass (permute π A) := by
  rw [tensorClass_permute, tensorClass_product_scalarShape, ← tensorClass_permute]

def neighborOutput (r b : ℕ+) (hb : 2 ≤ (b : ℕ)) (i : Fin 2) : FiniteTensor K :=
  if i = 0 then convolution r ⟨(b : ℕ) + 1, by omega⟩
  else convolution r ⟨(b : ℕ) - 1, by omega⟩

/-- The neighboring-length degeneration keeps its two intrinsic output blocks. -/
def convolutionNeighborIdentity (r b : ℕ+) (hb : 2 ≤ (b : ℕ)) :
    SharedLegIdentity (convolution (K := K) r b) (neighborOutput r b hb)
      dotShape (fun _ => scalarShape) := by
  classical
  apply sharedFirstPairIdentity
    (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) + 1))
    (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) - 1))
    (convolution r b) (neighborOutput r b hb) dotShape (fun _ => scalarShape)
    .xyz (fun _ => .xyz)
  · exact convolution_neighbor_degeneration r b hb
  · change ClassDegenerates
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) + 1)))
      (tensorClass (product (neighborOutput r b hb 0) scalarShape.tensor))
    rw [tensorClass_product_scalarShape]
    simp only [neighborOutput, ite_true]
    change ClassDegenerates
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) + 1)))
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) + 1)))
    exact ClassDegenerates.refl _
  · change ClassDegenerates
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) - 1)))
      (tensorClass (product (neighborOutput r b hb 1) scalarShape.tensor))
    rw [tensorClass_product_scalarShape]
    have hi : (1 : Fin 2) ≠ 0 := by decide
    simp only [neighborOutput, if_neg hi]
    change ClassDegenerates
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) - 1)))
      (classOf (OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r ((b : ℕ) - 1)))
    exact ClassDegenerates.refl _

def triplingOutputPermutation (i : Fin 3) : LegPermutation := if i = 1 then .xzy else .xyz

/-- The middle reversal is consumed only as its individual block map. -/
def convolutionTriplingIdentity (r : ℕ+) (hr : 2 ≤ (r : ℕ)) :
    SharedLegIdentity
      (convolution (K := K) r ⟨4 * (r : ℕ) - 1, by omega⟩)
      (fun _ : Fin 3 => convolution r r) scalarShape (fun _ => scalarShape) := by
  classical
  let C := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r r
  apply sharedFirstThreeIdentity C (fun (x : Fin (r : ℕ)) z y => C x.rev y z) C
    (convolution r ⟨4 * (r : ℕ) - 1, by omega⟩)
    (fun _ : Fin 3 => convolution r r) scalarShape (fun _ => scalarShape)
    .xyz triplingOutputPermutation
  · have hp : Degenerates
        (product (convolution (K := K) r ⟨4 * (r : ℕ) - 1, by omega⟩) scalarShape.tensor)
        (convolution r ⟨4 * (r : ℕ) - 1, by omega⟩) := by
      apply (classDegenerates_tensorClass_iff _ _).1
      rw [tensorClass_product_scalarShape]
      exact ClassDegenerates.refl _
    exact hp.trans (convolution_tripling_degeneration r hr)
  · rw [tensorClass_permute_product_scalarShape]
    simpa [triplingOutputPermutation, permute, convolution, C, classOf] using
      (ClassDegenerates.refl (classOf C))
  · rw [tensorClass_permute_product_scalarShape]
    have he := (tripling_middle_isomorphism (K := K) r).tensorClass_eq
    change classOf (fun (x : Fin (r : ℕ)) z y => C x.rev y z) =
      tensorClass (permute .xzy (convolution r r)) at he
    change ClassDegenerates (classOf (fun (x : Fin (r : ℕ)) z y => C x.rev y z))
      (tensorClass (permute .xzy (convolution r r)))
    rw [he]
    exact ClassDegenerates.refl _
  · rw [tensorClass_permute_product_scalarShape]
    simpa [triplingOutputPermutation, permute, convolution, C, classOf] using
      (ClassDegenerates.refl (classOf C))

end BlockIdentities.Square
