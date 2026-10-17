/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedSharedPermutation
public import BlockIdentities.Rectangular.ExtractionFiniteValue
public import BlockIdentities.Rectangular.ExtractionLogLimits
public import BlockIdentities.Square.ExtractionDimensionRates

/-! Actual probability-type schedules for shared-leg oriented entropy, with
an optional global physical permutation and its genuinely moved dot factor. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped BigOperators Topology
variable {F : Type*} [Field F]

/-- The shared-leg entropy estimate on every globally placed physical leg.
The actual products AD and B_i E_i precede all their permutations. -/
theorem oriented_shared_entropy_permute
    {ι : Type} [Fintype ι] (S : InteriorSupport F)
    (A : TensorOf F) (B : ι → TensorOf F) (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) (π : LegPermutation) :
    Real.log (orientedValue S
      (((A.product D.nonzeroTensor).permute identity.sourcePermutation).permute π)) ≥
        S.weight (sharedPhysicalAxis π) * finiteEntropy q +
          ∑ i, q i * Real.log (orientedValue S
            ((((B i).product (E i).nonzeroTensor).permute (identity.outputPermutation i)).permute π)) := by
  classical
  obtain ⟨N, hn, hntop, hemp, hwords⟩ := exists_floorTypeCounts_schedule q hq hsum
  let counts := floorTypeCounts q N
  let n : ℕ → ℕ := fun j => ∑ i, counts j i
  let M : ℕ → ℕ := fun j => Fintype.card (ExactWords (counts j))
  have hM (j : ℕ) : 1 ≤ M j :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (exactWords_card_pos (counts j)))
  let U : TensorOf F := ((A.product D.nonzeroTensor).permute identity.sourcePermutation).permute π
  let V : ι → TensorOf F := fun i =>
    (((B i).product (E i).nonzeroTensor).permute (identity.outputPermutation i)).permute π
  let Q : ℕ → MatrixShape := fun j => sharedPhysicalDotShape π (M j) (hM j)
  let L : ℕ → List (TensorOf F) := fun j =>
    List.ofFn (fun l : Fin (Fintype.card ι) => (V ((Fintype.equivFin ι).symm l)).power
      (counts j ((Fintype.equivFin ι).symm l)))
  have hU : U.val = permute π (permute identity.sourcePermutation (product A.val D.tensor)) := rfl
  have hV (i : ι) : (V i).val =
      permute π (permute (identity.outputPermutation i) (product (B i).val (E i).tensor)) := rfl
  have hL (j : ℕ) : (NonzeroTensor.tensorProductList (L j)).val =
      tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
        power (permute π (permute (identity.outputPermutation ((Fintype.equivFin ι).symm l))
          (product (B ((Fintype.equivFin ι).symm l)).val (E ((Fintype.equivFin ι).symm l)).tensor)))
          (counts j ((Fintype.equivFin ι).symm l)))) := by
    simp only [NonzeroTensor.tensorProductList, L, List.map_ofFn, Function.comp_apply,
      NonzeroTensor.power, hV]
    rfl
  have hfinite (j : ℕ) : ((1 : ℕ) : ℝ) * matrixWeight S (Q j) *
      ∏ i, orientedValue S (V i) ^ counts j i ≤
        ((6 : ℕ) : ℝ) ^ (∑ i, S.weight i) * orientedValue S U ^ n j * (1 : ℝ) := by
    have hc0 := shared_extraction_conversion_permute identity (counts j) π
    have hc : AsymptoticallyRestricts
        (copies 6 (product (power U.val (n j)) scalarShape.tensor))
        (copies 1 (product (NonzeroTensor.tensorProductList (L j)).val (Q j).tensor)) := by
      apply hc0.congr_classes
      · rw [hU]
        simp only [tensorClass_copies_eq, tensorClass_product_eq, tensorClass_power_eq,
          tensorClass_matrixShape_scalar, mul_one]
        rfl
      · rw [hL]
        simp only [tensorClass_copies_eq, Nat.cast_one, one_mul]
        rfl
    have hv := ordered_extraction_finite_value_bound S U (L j) scalarShape (Q j)
      (n j) 6 1 (by norm_num) le_rfl hc
    have hp : ((L j).map (orientedValue S)).prod = ∏ i, orientedValue S (V i) ^ counts j i := by
      calc
        _ = ∏ l : Fin (Fintype.card ι),
            orientedValue S (V ((Fintype.equivFin ι).symm l)) ^
              counts j ((Fintype.equivFin ι).symm l) := by
          simp only [L, List.map_ofFn, List.prod_ofFn, Function.comp_apply, orientedValue_power]
        _ = _ := (Fintype.equivFin ι).symm.prod_comp
          (fun i => orientedValue S (V i) ^ counts j i)
    rw [hp, matrixWeight_scalar] at hv
    exact hv
  have hw : Tendsto (fun j => (Real.log (matrixWeight S (Q j)) - Real.log (1 : ℝ)) /
      (n j : ℝ)) atTop (𝓝 (S.weight (sharedPhysicalAxis π) * finiteEntropy q)) := by
    have hx := hwords.const_mul (S.weight (sharedPhysicalAxis π))
    apply hx.congr
    intro j
    have hp : 0 < (M j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hM j))
    rw [show matrixWeight S (Q j) = (M j : ℝ) ^ S.weight (sharedPhysicalAxis π) from
      matrixWeight_sharedPhysicalDotShape S π (M j) (hM j), Real.log_rpow hp,
      Real.log_one, sub_zero]
    ring
  have hresult := ordered_extraction_log_limit (orientedValue S U)
    (fun i => orientedValue S (V i))
    (lt_of_lt_of_le zero_lt_one (one_le_orientedValue S U))
    (fun i => lt_of_lt_of_le zero_lt_one (one_le_orientedValue S (V i)))
    (∑ i, S.weight i) (fun _ => (1 : ℝ)) (fun j => matrixWeight S (Q j))
    (fun _ => zero_lt_one) (fun j => matrixWeight_pos S (Q j))
    n (fun _ => 6) (fun _ => 1) (fun i j => counts j i) hn
    (fun _ => by norm_num) (fun _ => le_rfl) hfinite q 0
    (S.weight (sharedPhysicalAxis π) * finiteEntropy q)
    (constant_overhead_log_rate n hntop 6) hemp
    (by simp only [Nat.cast_one, Real.log_one, zero_div]; exact tendsto_const_nhds) hw
  change Real.log (orientedValue S U) ≥
    S.weight (sharedPhysicalAxis π) * finiteEntropy q +
      ∑ i, q i * Real.log (orientedValue S (V i))
  linarith only [hresult]

/-- The exact unfactored, unrotated shared-leg entropy conclusion. -/
theorem oriented_shared_entropy
    {ι : Type} [Fintype ι] (S : InteriorSupport F)
    (A : TensorOf F) (B : ι → TensorOf F) (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    Real.log (orientedValue S ((A.product D.nonzeroTensor).permute identity.sourcePermutation)) ≥
      S.weight 0 * finiteEntropy q +
        ∑ i, q i * Real.log (orientedValue S
          (((B i).product (E i).nonzeroTensor).permute (identity.outputPermutation i))) := by
  exact oriented_shared_entropy_permute S A B D E identity q hq hsum .xyz

/-- Entropy optimization gives the actual powered shared-leg inequality on
any physical shared leg with positive support weight. -/
theorem oriented_shared_powered_permute
    {ι : Type} [Fintype ι] (S : InteriorSupport F)
    (A : TensorOf F) (B : ι → TensorOf F) (D : MatrixShape) (E : ι → MatrixShape)
    (identity : SharedLegIdentity A.val (fun i => (B i).val) D E)
    (π : LegPermutation) (hp : 0 < S.weight (sharedPhysicalAxis π)) :
    (∑ i, orientedValue S
      ((((B i).product (E i).nonzeroTensor).permute (identity.outputPermutation i)).permute π) ^
        (1 / S.weight (sharedPhysicalAxis π))) ≤
      orientedValue S (((A.product D.nonzeroTensor).permute identity.sourcePermutation).permute π) ^
        (1 / S.weight (sharedPhysicalAxis π)) := by
  let p := S.weight (sharedPhysicalAxis π)
  let U : TensorOf F := ((A.product D.nonzeroTensor).permute identity.sourcePermutation).permute π
  let V : ι → TensorOf F := fun i =>
    (((B i).product (E i).nonzeroTensor).permute (identity.outputPermutation i)).permute π
  have hp' : 0 < p := hp
  have hscale : 3 / (3 * p) = 1 / p := by field_simp [hp'.ne']
  have hx := normalizedValue_sum_le_of_entropy_bounds
    (orientedValue S U) (fun i => orientedValue S (V i)) (fun _ : ι => (1 : ℝ)) 1 (3 * p)
    (lt_of_lt_of_le zero_lt_one (one_le_orientedValue S U))
    (fun i => lt_of_lt_of_le zero_lt_one (one_le_orientedValue S (V i)))
    (fun _ => zero_lt_one) zero_lt_one (by dsimp [p]; positivity) (by
      intro q hq hsum
      have he := oriented_shared_entropy_permute S A B D E identity q hq hsum π
      simp only [Real.log_one, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
      change (∑ i, q i * Real.log (orientedValue S (V i))) +
        (3 * p) * (finiteEntropy q / 3) ≤ Real.log (orientedValue S U)
      nlinarith only [he])
  simpa only [hscale, one_mul] using hx

end BlockIdentities.Rectangular
