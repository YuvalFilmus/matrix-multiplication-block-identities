/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.InteriorSupportExists

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem interior_support_exists {F : Type*} [Field F]
    (v : Axis → ℝ≥0) (hv : ∀ i, 0 < v i) :
  ∃ S : InteriorSupport F, S.direction = v :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.interior_support_exists (F := F) v hv
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
