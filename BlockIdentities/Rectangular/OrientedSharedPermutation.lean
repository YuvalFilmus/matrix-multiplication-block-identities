/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.OrientedSharedExtraction
public import BlockIdentities.Tensor.PermutationClasses
public import BlockIdentities.Rectangular.OrientedGainOperations
public import BlockIdentities.Rectangular.OrientedWeights

/-! Global physical permutation of the actual finite shared-leg extraction.
No oriented-value permutation invariance is asserted. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {K : Type*} [Field K]

theorem permuteClass_one_eq (π : LegPermutation) : permuteClass π (1 : TensorClass K) = 1 := by
  cases π <;> simp only [permuteClass, cycleClass_one, swapClass_one]

theorem permuteClass_natCast_eq (π : LegPermutation) (m : ℕ) :
    permuteClass π (m : TensorClass K) = m := by
  cases π <;> simp only [permuteClass, cycleClass_natCast, swapClass_natCast]

theorem permuteClass_pow_eq (π : LegPermutation) (a : TensorClass K) (n : ℕ) :
    permuteClass π (a ^ n) = permuteClass π a ^ n := by
  induction n with
  | zero => simp only [pow_zero, permuteClass_one_eq]
  | succ n ih => rw [pow_succ, permuteClass_mul, ih, pow_succ]

theorem permuteClass_prod_eq {ι : Type*} (π : LegPermutation) (s : Finset ι)
    (a : ι → TensorClass K) :
    permuteClass π (∏ i ∈ s, a i) = ∏ i ∈ s, permuteClass π (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, permuteClass_one_eq]
  | @insert i s hi ih => rw [Finset.prod_insert hi, permuteClass_mul, ih, Finset.prod_insert hi]

/-- Each actual local degeneration in the all-power schedule is permuted. -/
theorem asymptoticallyRestricts_permute {A B : FiniteTensor K}
    (h : AsymptoticallyRestricts A B) (π : LegPermutation) :
    AsymptoticallyRestricts (permute π A) (permute π B) := by
  obtain ⟨a, ha, hrate, hc⟩ := (asymptoticallyRestricts_iff_classes A B).mp h
  apply (asymptoticallyRestricts_iff_classes _ _).mpr
  refine ⟨a, ha, hrate, ?_⟩
  intro n hn
  have hp := (hc n hn).permute π
  rw [permuteClass_mul, permuteClass_natCast_eq, permuteClass_pow_eq,
    permuteClass_pow_eq] at hp
  simpa only [tensorClass_permute] using hp

/-- Actual location of the original shared first leg after a global permutation. -/
def sharedPhysicalAxis : LegPermutation → Axis
  | .xyz => 0 | .xzy => 0 | .yxz => 1 | .yzx => 2 | .zxy => 1 | .zyx => 2

/-- Literal matrix shape of the retained M-dot on that physical axis. -/
def sharedPhysicalDotShape (π : LegPermutation) (M : ℕ) (hM : 1 ≤ M) : MatrixShape :=
  match π with
  | .xyz | .xzy => ⟨1, 1, M, by omega, by omega, by omega⟩
  | .yxz | .zxy => ⟨M, 1, 1, by omega, by omega, by omega⟩
  | .yzx | .zyx => ⟨1, M, 1, by omega, by omega, by omega⟩

private theorem cycle_matrix_class (a b c : ℕ) :
    cycleClass (tensorClass (matrix (K := K) a b c)) = tensorClass (matrix b c a) := by
  change cycleClass (classOf (Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) =
    classOf (Tensor.matrixCoefficients (K := K) (Fin b) (Fin c) (Fin a))
  rw [cycleClass_classOf]
  congr 1
  funext x y z
  exact Tensor.matrixCoefficients_cyclic x y z

private theorem swap_matrix_class (a b c : ℕ) :
    swapClass (tensorClass (matrix (K := K) a b c)) = tensorClass (matrix b a c) := by
  change swapClass (classOf (matrixMultiplicationTensor (K := K) a b c)) =
    classOf (matrixMultiplicationTensor (K := K) b a c)
  rw [swapClass_classOf]
  apply classOf_eq_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  funext x y z
  simp [Tensor.pullback, swapLast, matrixMultiplicationTensor, eq_comm, and_assoc, and_comm, and_left_comm] <;> rfl

theorem permute_dot_matrix_class (π : LegPermutation) (M : ℕ) (hM : 1 ≤ M) :
    tensorClass (permute π (matrix (K := K) 1 1 M)) =
      tensorClass ((sharedPhysicalDotShape π M hM).tensor (K := K)) := by
  rw [tensorClass_permute]
  cases π <;> simp only [permuteClass, sharedPhysicalDotShape,
    swap_matrix_class, cycle_matrix_class] <;> rfl

theorem matrixWeight_sharedPhysicalDotShape {F : Type*} [Field F] (S : InteriorSupport F)
    (π : LegPermutation) (M : ℕ) (hM : 1 ≤ M) :
    matrixWeight S (sharedPhysicalDotShape π M hM) = (M : ℝ) ^ S.weight (sharedPhysicalAxis π) := by
  cases π <;> simp [matrixWeight, sharedPhysicalDotShape, sharedPhysicalAxis]

/-- All blocks and their matrix factors retain their original order before the
individual permutation and the global physical placement. The final dot is the
actual matrix on the globally moved shared leg. -/
theorem shared_extraction_conversion_permute [Infinite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : FiniteTensor K} {B : ι → FiniteTensor K} {D : MatrixShape} {E : ι → MatrixShape}
    (identity : SharedLegIdentity A B D E) (counts : ι → ℕ) (π : LegPermutation) :
    AsymptoticallyRestricts
      (copies 6 (power (permute π (permute identity.sourcePermutation (product A D.tensor)))
        (∑ i, counts i)))
      (product (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
        let i := (Fintype.equivFin ι).symm l
        power (permute π (permute (identity.outputPermutation i) (product (B i) (E i).tensor)))
          (counts i))))
        (sharedPhysicalDotShape π (Fintype.card (ExactWords counts))
          (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos counts)))).tensor) := by
  classical
  let M := Fintype.card (ExactWords counts)
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos counts))
  have h := asymptoticallyRestricts_permute (identity.oriented_extraction_conversion counts) π
  have hdot : permuteClass π (tensorClass (matrix (K := K) 1 1 M)) =
      tensorClass ((sharedPhysicalDotShape π M hM).tensor (K := K)) :=
    (tensorClass_permute π (matrix (K := K) 1 1 M)).symm.trans (permute_dot_matrix_class π M hM)
  apply h.congr_classes
  · simp only [tensorClass_permute, tensorClass_copies_eq, tensorClass_power_eq,
      permuteClass_mul, permuteClass_natCast_eq, permuteClass_pow_eq]
  · simp only [tensorClass_permute_product, tensorClass_product_eq,
      tensorClass_permute, tensorClass_tensorProductList_ofFn, tensorClass_power_eq,
      permuteClass_mul, permuteClass_prod_eq, permuteClass_pow_eq]
    rw [hdot]

end BlockIdentities.Rectangular
