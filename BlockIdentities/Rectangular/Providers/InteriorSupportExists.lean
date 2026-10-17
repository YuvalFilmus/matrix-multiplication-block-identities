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

theorem interior_support_exists {F : Type*} [Field F]
    (v : Axis → ℝ≥0) (hv : ∀ i, 0 < v i) :
  ∃ S : InteriorSupport F, S.direction = v :=
by
  exact exists_interior_support v hv

end BlockIdentities.Rectangular.Providers
