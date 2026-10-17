/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedProfileCompletion
public import BlockIdentities.Rectangular.ProfileAngularAssembly
public import BlockIdentities.Rectangular.SupportOptimization

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem support_angular_constraint {F : Type*} [Field F]
    (S : InteriorSupport F) :
  (Real.pi / 2 : ℝ) ≤ ∑ i, Real.arccos (Real.sqrt (S.weight i)) :=
by
  by_cases hz : ∃ i, S.weight i = 0
  · obtain ⟨i, hi⟩ := hz
    exact support_angles_ge_of_weight_zero S i hi
  have hpositive : ∀ i, 0 < S.weight i := by
    intro i
    rcases lt_or_eq_of_le (interiorSupport_weight_bounds S i).1 with h | h
    · exact h
    · exact False.elim (hz ⟨i, h.symm⟩)
  obtain ⟨g, _, _, hg, hhom, hswap, _, hconc, hmono, htri⟩ :=
    exists_oriented_convolution_profile_laws S hpositive
  exact angular_of_six_profile_laws S.weight (interiorSupport_weight_bounds S)
    hpositive g hg hhom hswap hconc hmono htri

end BlockIdentities.Rectangular.Providers
