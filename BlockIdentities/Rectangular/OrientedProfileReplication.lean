/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedConvolutionProfiles
public import BlockIdentities.Rectangular.OrientedValueCopiesLower
public import BlockIdentities.Tensor.ConvolutionReplicationFinite

/-! Actual independent-copy lower bounds and physical convolution replication. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Natural tensor classes count independent scalars and remain fixed by actual
physical leg permutations, in every characteristic. -/
theorem permuteClass_natCast (π : LegPermutation) (m : ℕ) :
    permuteClass π (m : TensorClass (AlgebraicClosure F)) = m := by
  cases π <;> simp only [permuteClass, cycleClass_natCast, swapClass_natCast]

/-- The polynomial replication maps move with the physical leg permutation;
the target is still m independent copies of that same oriented tensor. -/
theorem orientedConvolution_replication_classes (π : LegPermutation) (m r s : ℕ+) :
    ClassDegenerates
      (tensorClass (orientedConvolution (F := F) π (m * r) (m * s)).val)
      (tensorClass ((orientedConvolution (F := F) π r s).copies m
        (by exact m.property)).val) := by
  have hd := convolution_replication_of_infinite (K := AlgebraicClosure F) m r s
  have hc := ((classDegenerates_tensorClass_iff _ _).mpr hd).permute π
  change ClassDegenerates
    (tensorClass (permute π (convolution (K := AlgebraicClosure F) (m * r) (m * s))))
    (tensorClass (copies m (permute π (convolution (K := AlgebraicClosure F) r s))))
  rw [tensorClass_permute, tensorClass_copies_eq, tensorClass_permute]
  simpa only [tensorClass_copies_eq, permuteClass_mul, permuteClass_natCast] using hc

/-- Replication increases the actual fixed-support profile by its full scale. -/
theorem convolutionProfile_replication (S : InteriorSupport F) (π : LegPermutation)
    (m r s : ℕ+) :
    (m : ℝ) * convolutionProfile S π r s ≤ convolutionProfile S π (m * r) (m * s) := by
  let T : TensorOf F := orientedConvolution π r s
  let U : TensorOf F := orientedConvolution π (m * r) (m * s)
  have hc := orientedConvolution_replication_classes (F := F) π m r s
  have hmono := orientedValue_mono S U (T.copies m m.property)
    (asymptoticallyRestricts_of_classDegenerates hc)
  exact (mul_orientedValue_le_copies S T m m.property).trans hmono

end BlockIdentities.Rectangular
