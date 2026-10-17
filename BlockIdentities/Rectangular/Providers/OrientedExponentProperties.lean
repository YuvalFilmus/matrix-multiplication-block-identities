/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGeometry

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_exponent_properties {F : Type*} [Field F] :

    orientedExponent F 0 = 0 ∧
    (∀ u v, orientedExponent F (u + v) ≤ orientedExponent F u + orientedExponent F v) ∧
    (∀ (t : ℝ≥0) u, orientedExponent F (t • u) = (t : ℝ) * orientedExponent F u) ∧
    (∀ u v, (∀ i, u i ≤ v i) → orientedExponent F u ≤ orientedExponent F v) ∧
    (∀ u i (t : ℝ≥0),
      0 ≤ orientedExponent F (u + Pi.single i t) - orientedExponent F u ∧
      orientedExponent F (u + Pi.single i t) - orientedExponent F u ≤ (t : ℝ)) :=
by
  exact ⟨orientedExponent_zero, orientedExponent_add_le, orientedExponent_smul,
    orientedExponent_mono, orientedExponent_single_increment⟩

end BlockIdentities.Rectangular.Providers
