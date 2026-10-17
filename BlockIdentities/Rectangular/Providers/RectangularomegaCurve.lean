/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Frozen.formalRectangularOmega_curve
public import BlockIdentities.Arithmetic.RectangularBasics

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem rectangularOmega_curve (F : Type*) [Field F] (k : ℝ) (hk : 0 ≤ k) :
  OAI.MatrixMultiplication.Arithmetic.rectangularOmega F k ≤ (if k ≤ (1 : ℝ) / 2 then 2 else 1 + k + 1 / (4 * k)) :=
by
  exact (Arithmetic.rectangularOmega_le_formalRectangularOmega (F := F) k).trans
    (BlockIdentities.Rectangular.formalRectangularOmega_curve F k hk)

end BlockIdentities.Rectangular.Providers
