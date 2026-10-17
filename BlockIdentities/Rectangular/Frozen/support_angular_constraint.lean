/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.SupportAngularConstraint

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem support_angular_constraint {F : Type*} [Field F]
    (S : InteriorSupport F) :
  (Real.pi / 2 : ℝ) ≤ ∑ i, Real.arccos (Real.sqrt (S.weight i)) :=
-- BEGIN APPROVED PROOF REGION
by
  exact Providers.support_angular_constraint S
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
