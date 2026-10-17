/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGainRankLimit

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_value_rank {F : Type*} [Field F]
    (S : InteriorSupport F) (T : TensorOf F) :
  (orientedGains S T).Nonempty ∧ BddAbove (orientedGains S T) ∧
      1 ≤ orientedValue S T ∧ orientedValue S T ≤ tensorAsymptoticRank T ∧
      ∀ r : ℕ, BorderRankAtMost T.val r → tensorAsymptoticRank T ≤ (r : ℝ) :=
by
  exact ⟨orientedGains_nonempty S T, orientedGains_bddAbove S T,
    one_le_orientedValue S T, orientedValue_le_tensorAsymptoticRank S T,
    fun _ hborder => tensorAsymptoticRank_le_of_borderRankAtMost T hborder⟩

end BlockIdentities.Rectangular.Providers
