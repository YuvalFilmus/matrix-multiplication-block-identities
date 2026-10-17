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

theorem support_weight_bounds {F : Type*} [Field F]
    (S : InteriorSupport F) :
  ∀ i, S.weight i ∈ Set.Icc (0 : ℝ) 1 :=
by
  exact interiorSupport_weight_bounds S

end BlockIdentities.Rectangular.Providers
