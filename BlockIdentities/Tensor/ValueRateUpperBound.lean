/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ExtractionRates
public import BlockIdentities.Tensor.CyclicValueWitness
public import BlockIdentities.Providers.RankAndField
public import BlockIdentities.Square.ValueYieldNumerics

/-! Ordinary value is bounded by any upper bound on genuine matrix rates. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {K : Type*} [Field K]

theorem valueAtOmega_le_of_matrixRate_bounds [IsAlgClosed K]
    (A : NonzeroTensor K)
    (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    (R : ℝ) (hR : 1 ≤ R)
    (hbound : ∀ r : ℝ, MatrixRate A.val r → r ≤ R) :
    valueAtOmega A ≤ R ^ Arithmetic.formalOmega K := by
  apply csSup_le (value_witnesses_nonempty A _)
  rintro v ⟨n, h, m, hn, hh, hm, hex, rfl⟩
  have hk : 1 ≤ 3 * n := by omega
  have hν : 0 < Arithmetic.formalOmega K := by
    have := Arithmetic.formalOmega_mem_Icc (F := K)
    linarith [this.1]
  have he := cyclic_value_extraction hcycle hex
  have hnum := matrixValueGain_le_of_rate_upper (Arithmetic.formalOmega K) hν
    (3 * n) hk h hh m hm R hR (by
      intro ε hε r hr hmargin
      apply hbound r
      apply matrixRate_of_fixed_extraction A.property hk hh hm he ε hε r hr
      simpa only [← Providers.formalOmega_eq_exactRankExponent K] using hmargin)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnum

end BlockIdentities.Square
