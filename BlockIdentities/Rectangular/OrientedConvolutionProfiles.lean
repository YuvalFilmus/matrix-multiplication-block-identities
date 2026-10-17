/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedValueOperations
public import BlockIdentities.Tensor.ConvolutionTerminal
public import BlockIdentities.Tensor.ConvolutionRankBound
public import BlockIdentities.Tensor.PermutationClasses
public import BlockIdentities.Tensor.Isomorphism

/-! Literal six oriented convolution profiles. Each orientation remembers the
physical locations of both short input legs; no equal-leg fallback is present. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

/-- Physical location of the first, length-r input after the displayed permutation. -/
def convolutionLeftAxis : LegPermutation → Axis
  | .xyz => 0 | .xzy => 0 | .yxz => 1 | .yzx => 2 | .zxy => 1 | .zyx => 2

/-- Physical location of the second, length-s input. -/
def convolutionRightAxis : LegPermutation → Axis
  | .xyz => 1 | .xzy => 2 | .yxz => 0 | .yzx => 0 | .zxy => 2 | .zyx => 1

theorem convolution_axes_distinct (π : LegPermutation) :
    convolutionLeftAxis π ≠ convolutionRightAxis π := by cases π <;> decide

/-- Exchange the two intrinsic input labels, preserving their physical locations. -/
def convolutionSwapInputs : LegPermutation → LegPermutation
  | .xyz => .yxz | .yxz => .xyz | .xzy => .yzx | .yzx => .xzy
  | .zxy => .zyx | .zyx => .zxy

@[simp] theorem convolutionSwapInputs_twice (π : LegPermutation) :
    convolutionSwapInputs (convolutionSwapInputs π) = π := by cases π <;> rfl

@[simp] theorem convolutionLeftAxis_swap (π : LegPermutation) :
    convolutionLeftAxis (convolutionSwapInputs π) = convolutionRightAxis π := by cases π <;> rfl

@[simp] theorem convolutionRightAxis_swap (π : LegPermutation) :
    convolutionRightAxis (convolutionSwapInputs π) = convolutionLeftAxis π := by cases π <;> rfl

/-- The actual oriented finite coefficient tensor on the six valid physical pairs. -/
def orientedConvolution (π : LegPermutation) (r s : ℕ+) : TensorOf F :=
  (nonzeroConvolution (K := AlgebraicClosure F) r s).permute π

/-- Literal value, with S fixed while the physical orientation varies. -/
def convolutionProfile (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) : ℝ :=
  orientedValue S (orientedConvolution π r s)

theorem one_le_convolutionProfile (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) :
    1 ≤ convolutionProfile S π r s := one_le_orientedValue S _

private theorem rankAtMost_swapLast {K : Type*} [Field K] {A : FiniteTensor K} {R : ℕ}
    (h : Tensor.RankAtMost A.coeff R) : Tensor.RankAtMost (permute .xzy A).coeff R := by
  obtain ⟨a, b, c, h⟩ := h
  refine ⟨a, c, b, ?_⟩
  funext x z y
  change A.coeff x y z = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Tensor.rankOne]
  ring

/-- Permuting actual rank decompositions permutes their three coefficient vectors. -/
theorem rankAtMost_permute {K : Type*} [Field K] {A : FiniteTensor K} {R : ℕ}
    (h : Tensor.RankAtMost A.coeff R) (π : LegPermutation) :
    Tensor.RankAtMost (permute π A).coeff R := by
  cases π with
  | xyz => exact h
  | xzy => exact rankAtMost_swapLast h
  | yxz => exact (rankAtMost_swapLast h).cyclic.cyclic
  | yzx => exact h.cyclic
  | zxy => exact h.cyclic.cyclic
  | zyx => exact (rankAtMost_swapLast h).cyclic

/-- The upper bound charges the actual convolution coefficient rank. -/
theorem convolutionProfile_le_rank (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) :
    convolutionProfile S π r s ≤ ((r : ℕ) + (s : ℕ) - 1 : ℕ) := by
  have hr := rankAtMost_permute
    (convolution_coeff_rankAtMost (K := AlgebraicClosure F) r s) π
  have hv := (orientedValue_le_tensorAsymptoticRank S (orientedConvolution π r s)).trans
    (tensorAsymptoticRank_le_exactRank _)
  apply hv.trans
  have heq : (orientedConvolution (F := F) π r s).val =
      permute π (convolution (K := AlgebraicClosure F) r s) := rfl
  rw [heq]
  exact_mod_cast exactRank_le hr

/-- Input interchange is an actual coefficient isomorphism, followed by the
same physical placement. It is not invariance of V under a leg permutation. -/
theorem orientedConvolution_input_swap_class (π : LegPermutation) (r s : ℕ+) :
    tensorClass (orientedConvolution (F := F) π r s).val =
      tensorClass (orientedConvolution (F := F) (convolutionSwapInputs π) s r).val := by
  have hc := (convolution_input_swap_isomorphic (K := AlgebraicClosure F) r s).tensorClass_eq
  have hp := congrArg (permuteClass π) hc
  rw [← tensorClass_permute, ← tensorClass_permute] at hp
  cases π <;> exact hp

theorem convolutionProfile_input_swap (S : InteriorSupport F) (π : LegPermutation) (r s : ℕ+) :
    convolutionProfile S π r s = convolutionProfile S (convolutionSwapInputs π) s r :=
  orientedValue_eq_of_tensorClass_eq S _ _ (orientedConvolution_input_swap_class π r s)

/-- Literal subindices of the convolution polynomial are obtained by selecting
coordinates on each of its three legs. -/
theorem convolution_class_mono {K : Type*} [Field K] {r s R S : ℕ+}
    (hr : (r : ℕ) ≤ R) (hs : (s : ℕ) ≤ S) :
    tensorClass (convolution (K := K) r s) ≤ tensorClass (convolution R S) := by
  classical
  have hz : (r : ℕ) + (s : ℕ) - 1 ≤ (R : ℕ) + (S : ℕ) - 1 := by omega
  let T := OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) R S
  have hp := IsRestriction.pullback T (Fin.castLE hr) (Fin.castLE hs) (Fin.castLE hz)
  have heq : Tensor.pullback (Fin.castLE hr) (Fin.castLE hs) (Fin.castLE hz) T =
      OAI.MatrixMultiplication.AuxiliarySeparation.convolution (K := K) r s := by
    funext x y z
    rfl
  rw [heq] at hp
  exact (classOf_le_iff _ _).mpr hp

/-- Monotonicity is transported through the actual permutation of the maps. -/
theorem convolutionProfile_mono (S : InteriorSupport F) (π : LegPermutation)
    {r s R b : ℕ+} (hr : (r : ℕ) ≤ R) (hs : (s : ℕ) ≤ b) :
    convolutionProfile S π r s ≤ convolutionProfile S π R b := by
  have hc := (ClassDegenerates.of_le
    (convolution_class_mono (K := AlgebraicClosure F) hr hs)).permute π
  have hp : ClassDegenerates (tensorClass (orientedConvolution (F := F) π R b).val)
      (tensorClass (orientedConvolution (F := F) π r s).val) := by
    change ClassDegenerates
      (tensorClass (permute π (Square.convolution (K := AlgebraicClosure F) R b)))
      (tensorClass (permute π (Square.convolution (K := AlgebraicClosure F) r s)))
    simpa only [tensorClass_permute] using hc
  exact orientedValue_mono S _ _ (asymptoticallyRestricts_of_classDegenerates hp)

end BlockIdentities.Rectangular
