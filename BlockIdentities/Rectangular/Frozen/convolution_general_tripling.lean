/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.ConvolutionGeneralTripling

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem convolution_general_tripling {K : Type*} [Field K] (r s : ℕ+) :
  Degenerates
      (Square.convolution (K := K) r ⟨3 * (s : ℕ) + (r : ℕ) - 1, by
        show 0 < (3 * (s : ℕ) + (r : ℕ) - 1 : ℕ)
        have hr : 0 < (r : ℕ) := r.property
        have hs : 0 < (s : ℕ) := s.property
        omega⟩)
      (generalTriplingSplit r s) :=
-- BEGIN APPROVED PROOF REGION
by exact Providers.convolution_general_tripling r s
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
