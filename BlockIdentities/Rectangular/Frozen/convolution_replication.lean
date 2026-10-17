/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.ConvolutionReplication

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem convolution_replication {F : Type*} [Field F]
    (m r s : ℕ+) :
  Degenerates
      (Square.convolution (K := AlgebraicClosure F) (m * r) (m * s))
      (copies (m : ℕ) (Square.convolution r s)) :=
-- BEGIN APPROVED PROOF REGION
by exact BlockIdentities.Rectangular.Providers.convolution_replication (F := F) m r s
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
