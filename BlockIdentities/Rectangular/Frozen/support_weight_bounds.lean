/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.SupportWeightBounds

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem support_weight_bounds {F : Type*} [Field F]
    (S : InteriorSupport F) :
  ∀ i, S.weight i ∈ Set.Icc (0 : ℝ) 1 :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.support_weight_bounds (F := F) S
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
