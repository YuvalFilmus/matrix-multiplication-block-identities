/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Arithmetic.ShapeFieldDescent

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalShapeOmega_eq_algebraicClosure (F : Type*) [Field F] (a b c : ℝ≥0) :
  Arithmetic.formalShapeOmega F a b c =
      Arithmetic.formalShapeOmega (AlgebraicClosure F) a b c :=
by
  exact (Arithmetic.formalShapeOmega_algebraicClosure (F := F) a b c).symm

end BlockIdentities.Rectangular.Providers
