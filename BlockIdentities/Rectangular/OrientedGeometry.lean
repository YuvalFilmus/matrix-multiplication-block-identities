/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeCoordinateBound
public import BlockIdentities.Arithmetic.ShapeHomogeneity
public import BlockIdentities.Rectangular.SupportBounds

/-! The geometry of the actual ordered matrix exponent, derived from formally
correct programs and exact finite coefficient decompositions. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open scoped BigOperators NNReal
open BlockIdentities.Arithmetic
variable {F : Type*} [Field F]

theorem orientedExponent_zero : orientedExponent F 0 = 0 :=
  formalShapeOmega_zero_zero_zero

theorem orientedExponent_add_le (u v : Axis → ℝ≥0) :
    orientedExponent F (u + v) ≤ orientedExponent F u + orientedExponent F v :=
  formalShapeOmega_add_le (u 1) (u 2) (u 0) (v 1) (v 2) (v 0)

theorem orientedExponent_smul (t : ℝ≥0) (u : Axis → ℝ≥0) :
    orientedExponent F (t • u) = (t : ℝ) * orientedExponent F u :=
  formalShapeOmega_mul t (u 1) (u 2) (u 0)

theorem orientedExponent_mono (u v : Axis → ℝ≥0) (h : ∀ i, u i ≤ v i) :
    orientedExponent F u ≤ orientedExponent F v :=
  formalShapeOmega_mono (h 1) (h 2) (h 0)

theorem orientedExponent_single_increment (u : Axis → ℝ≥0) (i : Axis) (t : ℝ≥0) :
    0 ≤ orientedExponent F (u + Pi.single i t) - orientedExponent F u ∧
    orientedExponent F (u + Pi.single i t) - orientedExponent F u ≤ (t : ℝ) := by
  constructor
  · exact sub_nonneg.mpr (orientedExponent_mono u _ (by
      intro j
      exact le_add_of_nonneg_right (bot_le)))
  · have hupper : orientedExponent F (u + Pi.single i t) ≤ orientedExponent F u + (t : ℝ) := by
      fin_cases i
      · simpa [orientedExponent, Pi.single_apply] using
          formalShapeOmega_add_third_le (F := AlgebraicClosure F) (u 1) (u 2) (u 0) t
      · simpa [orientedExponent, Pi.single_apply] using
          formalShapeOmega_add_first_le (F := AlgebraicClosure F) (u 1) (u 2) (u 0) t
      · simpa [orientedExponent, Pi.single_apply] using
          formalShapeOmega_add_second_le (F := AlgebraicClosure F) (u 1) (u 2) (u 0) t
    linarith

theorem exists_interior_support (v : Axis → ℝ≥0) (hv : ∀ i, 0 < v i) :
    ∃ S : InteriorSupport F, S.direction = v := by
  have hvne : v ≠ 0 := by
    intro h
    have hh := hv 0
    simpa [h] using hh
  obtain ⟨p, hp, hc⟩ := exists_support_weights_of_sublinear (orientedExponent F)
    orientedExponent_zero orientedExponent_add_le orientedExponent_smul
    orientedExponent_mono v hvne
  exact ⟨⟨v, hv, p, hp, hc⟩, rfl⟩

theorem interiorSupport_weight_bounds (S : InteriorSupport F) :
    ∀ i, S.weight i ∈ Set.Icc (0 : ℝ) 1 :=
  support_weights_mem_Icc (orientedExponent F) S.direction S.direction_pos S.weight
    S.supporting S.touching orientedExponent_mono (by
      intro u i
      have h := (orientedExponent_single_increment (F := F) u i 1).2
      simpa only [NNReal.coe_one, add_comm] using (sub_le_iff_le_add.mp h))

end BlockIdentities.Rectangular
