/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.OrientedValueRank

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_value_rank {F : Type*} [Field F]
    (S : InteriorSupport F) (T : TensorOf F) :
  (orientedGains S T).Nonempty ∧ BddAbove (orientedGains S T) ∧
      1 ≤ orientedValue S T ∧ orientedValue S T ≤ tensorAsymptoticRank T ∧
      ∀ r : ℕ, BorderRankAtMost T.val r → tensorAsymptoticRank T ≤ (r : ℝ) :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.oriented_value_rank (F := F) S T
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
