/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Frozen.general_extraction_v3
public import BlockIdentities.Tensor.SharedExtractionConversion
public import BlockIdentities.Square.ExtractionDimensionRates
public import BlockIdentities.Tensor.ValueSymmetries

/-! Actual extraction schedules for the shared-leg entropy inequality. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {K : Type*} [Field K] [IsAlgClosed K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The conversion used in the entropy argument, on arbitrary genuine integral
counts. The single target copy is transported by actual tensor-class equality. -/
theorem SharedLegIdentity.entropy_schedule_conversion
    (A : NonzeroTensor K) (B : ι → NonzeroTensor K)
    {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (counts : ι → ℕ) :
    AsymptoticallyRestricts
      (copies 216 (product
        (power (symmetrize (A.permute identity.sourcePermutation).val) (∑ i, counts i))
        (square (D.volume ^ (∑ i, counts i)))))
      (copies 1 (product
        (square (Fintype.card (ExactWords counts) * ∏ i, (E i).volume ^ counts i))
        (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
          let i := (Fintype.equivFin ι).symm l
          power (symmetrize (permute (K := K) (identity.outputPermutation i) (B i).val))
            (counts i)))))) := by
  classical
  have hc := identity.extraction_conversion counts
  rw [asymptoticallyRestricts_iff_classes] at hc ⊢
  simpa only [tensorClass_copies_eq, Nat.cast_one, one_mul, NonzeroTensor.permute] using hc

/-- The shared-leg finite construction gives the entropy inequality for every
real probability law, via genuine fixed-offset integral type schedules. -/
theorem SharedLegIdentity.entropy_inequality
    (A : NonzeroTensor K) (B : ι → NonzeroTensor K)
    {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    Real.log (valueAtOmega A) ≥ (∑ i, p i * Real.log (valueAtOmega (B i))) +
      Arithmetic.formalOmega K *
        ((finiteEntropy p + ∑ i, p i * Real.log ((E i).volume : ℝ) -
          Real.log (D.volume : ℝ)) / 3) := by
  classical
  obtain ⟨N, hn, hntop, hemp, hwords⟩ := exists_floorTypeCounts_schedule p hp hsum
  let counts := floorTypeCounts p N
  let n : ℕ → ℕ := fun j => ∑ i, counts j i
  have hc : 1 ≤ D.volume := Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.mul_pos (Nat.mul_pos D.a_pos D.b_pos) D.c_pos))
  have hk (i : ι) : 1 ≤ (E i).volume := Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (Nat.mul_pos (Nat.mul_pos (E i).a_pos (E i).b_pos) (E i).c_pos))
  have hab := extractionDimension_rate counts hn p hemp hwords D.volume hc
    (fun i => (E i).volume) hk
  have hout := general_extraction (A.permute identity.sourcePermutation) B n
    (fun j => extractionInputDimension D.volume (counts j))
    (fun j => extractionOutputDimension (fun i => (E i).volume) (counts j))
    (fun _ => 216) (fun _ => 1) (fun i j => counts j i)
    (fun i _ => identity.outputPermutation i)
    hn
    (fun j => Nat.one_le_iff_ne_zero.mpr (ne_of_gt
      (extractionInputDimension_pos D.volume hc (counts j))))
    (fun j => Nat.one_le_iff_ne_zero.mpr (ne_of_gt
      (extractionOutputDimension_pos (fun i => (E i).volume) hk (counts j))))
    (fun _ => by norm_num) (fun _ => le_rfl) hntop
    (fun j => identity.entropy_schedule_conversion A B (counts j))
    p 0 ((finiteEntropy p + ∑ i, p i * Real.log ((E i).volume : ℝ) -
      Real.log (D.volume : ℝ)) / 3)
    (constant_overhead_log_rate n hntop 216) hemp
    (by simp only [Nat.cast_one, Real.log_one, zero_div]; exact tendsto_const_nhds)
    hab
  have hvalue : valueAtOmega (A.permute identity.sourcePermutation) = valueAtOmega A :=
    value_permute ⟨Arithmetic.formalOmega K, Arithmetic.formalOmega_mem_Icc (F := K)⟩
      A identity.sourcePermutation
  simpa only [hvalue, add_zero] using hout

end BlockIdentities.Square
