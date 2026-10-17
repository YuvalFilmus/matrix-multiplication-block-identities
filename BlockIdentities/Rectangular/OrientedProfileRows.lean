/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedSharedEntropy
public import BlockIdentities.Rectangular.OrientedProfileReplication
public import BlockIdentities.Tensor.OrientedConvolutionIdentities

/-! Actual powered neighboring and three-sector rows for all six physical
convolution orientations, retaining the distinct middle orientation. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators
variable {F : Type*} [Field F]

/-- The six orientations cover exactly every distinct ordered physical pair. -/
theorem exists_convolution_orientation (i j : Axis) (hij : i ≠ j) :
    ∃ π : LegPermutation, convolutionLeftAxis π = i ∧ convolutionRightAxis π = j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hij rfl)
    | exact ⟨.xyz, rfl, rfl⟩
    | exact ⟨.xzy, rfl, rfl⟩
    | exact ⟨.yxz, rfl, rfl⟩
    | exact ⟨.yzx, rfl, rfl⟩
    | exact ⟨.zxy, rfl, rfl⟩
    | exact ⟨.zyx, rfl, rfl⟩

/-- Globally place the side-swapped intrinsic convolution. -/
def convolutionSwapSides : LegPermutation → LegPermutation
  | .xyz => .xzy | .xzy => .xyz | .yxz => .zxy | .zxy => .yxz
  | .yzx => .zyx | .zyx => .yzx

theorem convolutionLeftAxis_swapSides (π : LegPermutation) :
    convolutionLeftAxis (convolutionSwapSides π) = convolutionLeftAxis π := by cases π <;> rfl

theorem sharedPhysicalAxis_eq_convolutionLeftAxis (π : LegPermutation) :
    sharedPhysicalAxis π = convolutionLeftAxis π := by cases π <;> rfl

theorem orientedValue_double_permute_product_scalar (S : InteriorSupport F) (A : TensorOf F)
    (δ π : LegPermutation) :
    orientedValue S (((A.product scalarShape.nonzeroTensor).permute δ).permute π) =
      orientedValue S ((A.permute δ).permute π) := by
  apply orientedValue_eq_of_tensorClass_eq
  change tensorClass (permute π (permute δ (product A.val scalarShape.tensor))) =
    tensorClass (permute π (permute δ A.val))
  simpa only [tensorClass_permute] using congrArg (permuteClass π)
    (tensorClass_permute_product_scalarShape δ A.val)

theorem orientedValue_permute_product_dot (S : InteriorSupport F) (A : TensorOf F)
    (π : LegPermutation) (M : ℕ) (hM : 1 ≤ M) :
    orientedValue S ((A.product (sharedPhysicalDotShape .xyz M hM).nonzeroTensor).permute π) =
      (M : ℝ) ^ S.weight (sharedPhysicalAxis π) * orientedValue S (A.permute π) := by
  let U : TensorOf F := (A.product (sharedPhysicalDotShape .xyz M hM).nonzeroTensor).permute π
  let V : TensorOf F := (A.permute π).product (sharedPhysicalDotShape π M hM).nonzeroTensor
  have hc : tensorClass U.val = tensorClass V.val := by
    change tensorClass (permute π (product A.val (matrix (K := AlgebraicClosure F) 1 1 M))) =
      tensorClass (product (permute π A.val) (sharedPhysicalDotShape π M hM).tensor)
    rw [tensorClass_permute_product, tensorClass_product_eq, permute_dot_matrix_class]
  have hv := orientedValue_eq_of_tensorClass_eq S U V hc
  rw [orientedValue_product_matrix, matrixWeight_sharedPhysicalDotShape] at hv
  exact hv

private theorem rpow_weighted_double {x p : ℝ} (hx : 0 ≤ x) (hp : 0 < p) :
    ((2 : ℝ) ^ p * x) ^ (1 / p) = 2 * x ^ (1 / p) := by
  have he : p * (1 / p) = 1 := by field_simp [hp.ne']
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) hx,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), he, Real.rpow_one]

theorem convolutionProfile_le_add (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) :
    convolutionProfile S π r s ≤ (r : ℝ) + s := by
  have h := convolutionProfile_le_rank S π r s
  have hn : (((r : ℕ) + (s : ℕ) - 1 : ℕ) : ℝ) ≤ ((r : ℕ) : ℝ) + ((s : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_le ((r : ℕ) + (s : ℕ)) 1)
  exact h.trans hn

/-- The diagonal integer scale of C(1,1), followed by actual subindices, gives
both-coordinate minimum growth for every physical orientation. -/
theorem min_le_convolutionProfile (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) :
    min (r : ℝ) (s : ℝ) ≤ convolutionProfile S π r s := by
  let m : ℕ+ := ⟨min (r : ℕ) (s : ℕ), lt_min r.property s.property⟩
  have hmr : (m : ℕ) ≤ r := min_le_left _ _
  have hms : (m : ℕ) ≤ s := min_le_right _ _
  have hrep : (m : ℝ) * convolutionProfile S π 1 1 ≤ convolutionProfile S π m m := by
    simpa only [mul_one] using convolutionProfile_replication S π m 1 1
  have hone := mul_le_mul_of_nonneg_left (one_le_convolutionProfile S π 1 1)
    (show 0 ≤ (m : ℝ) by positivity)
  have hmreal : min (r : ℝ) (s : ℝ) = (m : ℝ) := by
    dsimp only [m]
    norm_cast
  rw [hmreal]
  have hmul : (m : ℝ) ≤ (m : ℝ) * convolutionProfile S π 1 1 := by
    simpa only [mul_one] using hone
  exact hmul.trans (hrep.trans (convolutionProfile_mono S π hmr hms))

/-- Discrete concavity is derived from the actual two-block neighboring split. -/
theorem convolutionProfile_neighbor_powered (S : InteriorSupport F) (π : LegPermutation)
    (r s : ℕ+) (hs : 2 ≤ (s : ℕ)) (hp : 0 < S.weight (convolutionLeftAxis π)) :
    convolutionProfile S π r ⟨(s : ℕ) - 1, by omega⟩ ^ (1 / S.weight (convolutionLeftAxis π)) +
      convolutionProfile S π r ⟨(s : ℕ) + 1, by omega⟩ ^ (1 / S.weight (convolutionLeftAxis π)) ≤
        2 * convolutionProfile S π r s ^ (1 / S.weight (convolutionLeftAxis π)) := by
  classical
  let A : TensorOf F := nonzeroConvolution r s
  let B : Fin 2 → TensorOf F := fun i => ⟨neighborOutput r s hs i, by
    by_cases hi : i = 0
    · simpa only [neighborOutput, if_pos hi] using
        (nonzero_convolution (K := AlgebraicClosure F) r ⟨(s : ℕ) + 1, by omega⟩)
    · simpa only [neighborOutput, if_neg hi] using
        (nonzero_convolution (K := AlgebraicClosure F) r ⟨(s : ℕ) - 1, by omega⟩)⟩
  let identity : SharedLegIdentity A.val (fun i => (B i).val) dotShape (fun _ => scalarShape) :=
    convolutionNeighborIdentity r s hs
  have hp' : 0 < S.weight (sharedPhysicalAxis π) := by
    rw [sharedPhysicalAxis_eq_convolutionLeftAxis]; exact hp
  have hv := oriented_shared_powered_permute S A B dotShape (fun _ => scalarShape) identity π hp'
  have hsource : orientedValue S
      (((A.product dotShape.nonzeroTensor).permute identity.sourcePermutation).permute π) =
        (2 : ℝ) ^ S.weight (sharedPhysicalAxis π) * convolutionProfile S π r s := by
    change orientedValue S ((A.product (sharedPhysicalDotShape .xyz 2 (by norm_num)).nonzeroTensor).permute π) = _
    exact orientedValue_permute_product_dot S A π 2 (by norm_num)
  have houtput (i : Fin 2) : orientedValue S
      ((((B i).product scalarShape.nonzeroTensor).permute (identity.outputPermutation i)).permute π) =
      orientedValue S ((B i).permute π) := by
    change orientedValue S ((((B i).product scalarShape.nonzeroTensor).permute .xyz).permute π) = _
    exact orientedValue_double_permute_product_scalar S (B i) .xyz π
  simp_rw [houtput] at hv
  rw [hsource, sharedPhysicalAxis_eq_convolutionLeftAxis] at hv
  rw [rpow_weighted_double (le_trans zero_le_one (one_le_convolutionProfile S π r s)) hp] at hv
  have hB0 : B 0 = nonzeroConvolution (K := AlgebraicClosure F) r ⟨(s : ℕ) + 1, by omega⟩ := by
    apply Subtype.ext
    rfl
  have hB1 : B 1 = nonzeroConvolution (K := AlgebraicClosure F) r ⟨(s : ℕ) - 1, by omega⟩ := by
    apply Subtype.ext
    rfl
  rw [Fin.sum_univ_two, hB0, hB1] at hv
  have hv' :
      convolutionProfile S π r ⟨(s : ℕ) + 1, by omega⟩ ^ (1 / S.weight (convolutionLeftAxis π)) +
        convolutionProfile S π r ⟨(s : ℕ) - 1, by omega⟩ ^ (1 / S.weight (convolutionLeftAxis π)) ≤
          2 * convolutionProfile S π r s ^ (1 / S.weight (convolutionLeftAxis π)) := by
    exact hv
  linarith only [hv']

/-- The three-sector source row has two outer profiles and the distinct
side-swapped middle profile, on the same physical shared leg. -/
theorem convolutionProfile_tripling_powered (S : InteriorSupport F) (π : LegPermutation)
    (r s : ℕ+) (hp : 0 < S.weight (convolutionLeftAxis π)) :
    2 * convolutionProfile S π r s ^ (1 / S.weight (convolutionLeftAxis π)) +
      convolutionProfile S (convolutionSwapSides π) r s ^ (1 / S.weight (convolutionLeftAxis π)) ≤
        convolutionProfile S π r ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
          show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
          have hr : 0 < (r : ℕ) := r.property
          have hs : 0 < (s : ℕ) := s.property
          omega⟩ ^ (1 / S.weight (convolutionLeftAxis π)) := by
  classical
  let b : ℕ+ := ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
    show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
    have hr : 0 < (r : ℕ) := r.property
    have hs : 0 < (s : ℕ) := s.property
    omega⟩
  let A : TensorOf F := nonzeroConvolution r b
  let B : Fin 3 → TensorOf F := fun _ => nonzeroConvolution r s
  let identity : SharedLegIdentity A.val (fun i => (B i).val) scalarShape (fun _ => scalarShape) :=
    generalTriplingSharedIdentity r s
  have hp' : 0 < S.weight (sharedPhysicalAxis π) := by
    rw [sharedPhysicalAxis_eq_convolutionLeftAxis]; exact hp
  have hv := oriented_shared_powered_permute S A B scalarShape (fun _ => scalarShape) identity π hp'
  have hsource : orientedValue S
      (((A.product scalarShape.nonzeroTensor).permute identity.sourcePermutation).permute π) =
      convolutionProfile S π r b := by
    change orientedValue S (((A.product scalarShape.nonzeroTensor).permute .xyz).permute π) = _
    exact orientedValue_double_permute_product_scalar S A .xyz π
  have houtput (i : Fin 3) : orientedValue S
      ((((B i).product scalarShape.nonzeroTensor).permute (identity.outputPermutation i)).permute π) =
      orientedValue S (((B i).permute (triplingOutputPermutation i)).permute π) :=
    orientedValue_double_permute_product_scalar S (B i) (triplingOutputPermutation i) π
  simp_rw [houtput] at hv
  rw [hsource, sharedPhysicalAxis_eq_convolutionLeftAxis] at hv
  have hmiddle : orientedValue S (((nonzeroConvolution (K := AlgebraicClosure F) r s).permute .xzy).permute π) =
      convolutionProfile S (convolutionSwapSides π) r s := by cases π <;> rfl
  have houter : orientedValue S (((nonzeroConvolution (K := AlgebraicClosure F) r s).permute .xyz).permute π) =
      convolutionProfile S π r s := rfl
  have hv' : convolutionProfile S π r s ^ (1 / S.weight (convolutionLeftAxis π)) +
      (convolutionProfile S (convolutionSwapSides π) r s ^ (1 / S.weight (convolutionLeftAxis π)) +
        (convolutionProfile S π r s ^ (1 / S.weight (convolutionLeftAxis π)) + 0)) ≤
          convolutionProfile S π r b ^ (1 / S.weight (convolutionLeftAxis π)) := by
    simpa [Fin.sum_univ_succ, B, triplingOutputPermutation, hmiddle, houter] using hv
  linarith only [hv']

end BlockIdentities.Rectangular
