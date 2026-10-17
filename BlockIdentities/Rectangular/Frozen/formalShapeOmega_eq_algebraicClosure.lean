/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.FormalshapeomegaEqAlgebraicclosure

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem formalShapeOmega_eq_algebraicClosure (F : Type*) [Field F] (a b c : ℝ≥0) :
  Arithmetic.formalShapeOmega F a b c =
      Arithmetic.formalShapeOmega (AlgebraicClosure F) a b c :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.formalShapeOmega_eq_algebraicClosure F a b c
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
