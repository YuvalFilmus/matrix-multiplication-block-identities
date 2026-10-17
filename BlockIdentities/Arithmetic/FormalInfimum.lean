/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Arithmetic.FormalBounds

/-! Positive-slack admissibility at the formal infimum, over every field. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Arithmetic

open OAI.MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

/-- The formal infimum itself is admissible: approximate it within half the
requested slack and use the remaining half for the chosen admissible exponent.
This is an unconditional consequence of the cubic algorithm and the definition. -/
theorem formalAdmissibleExponent_formalOmega :
    FormalAdmissibleExponent F (formalOmega F) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hτlt⟩ := exists_lt_of_csInf_lt
    (s := {τ : ℝ | FormalAdmissibleExponent F τ})
    (formalAdmissibleExponent_nonempty (F := F))
    (show sInf {τ : ℝ | FormalAdmissibleExponent F τ} < formalOmega F + ε / 2 from
      by change formalOmega F < formalOmega F + ε / 2; linarith)
  obtain ⟨C, hC, hcost⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hPcost⟩ := hcost n hn
  refine ⟨P, hP, hPcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn
  · linarith

/-- The original input-correctness exponent is bounded by the formally correct
polynomial exponent, including for finite fields. Equality is not assumed. -/
theorem omega_le_formalOmega : omega F ≤ formalOmega F :=
  omega_le_of_admissibleExponent
    (formalAdmissibleExponent_formalOmega (F := F)).admissibleExponent

end BlockIdentities.Arithmetic
