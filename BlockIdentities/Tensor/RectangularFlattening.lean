/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.Definitions
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorFlattening
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorSymmetrization

/-! Finite entry-count lower bounds for an actual rectangular matrix rank seed. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
variable {K : Type*} [Field K]

/-- The three flattenings charge all input and output entries to the rank seed.
The fixed unused index exists because the matrix dimensions are positive. -/
theorem matrix_rankAtMost_entry_counts {a b c R : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := K) a b c) R) :
    a * b ≤ R ∧ b * c ≤ R ∧ c * a ≤ R := by
  let i₀ : Fin a := ⟨0, ha⟩
  let j₀ : Fin b := ⟨0, hb⟩
  let k₀ : Fin c := ⟨0, hc⟩
  have hab : a * b ≤ R := by
    have hminor : ∀ i j : Fin a × Fin b,
        Tensor.cyclic (matrixMultiplicationTensor (K := K) a b c)
          (i.2, k₀) (k₀, i.1) j = if i = j then 1 else 0 := by
      intro i j
      simp [Tensor.cyclic, matrixMultiplicationTensor, Prod.ext_iff, eq_comm, and_comm]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      h.cyclic.card_le_of_identity (fun i : Fin a × Fin b => (i.2, k₀))
        (fun i => (k₀, i.1)) id hminor
  have hbc : b * c ≤ R := by
    have hminor : ∀ i j : Fin b × Fin c,
        Tensor.cyclic (Tensor.cyclic (matrixMultiplicationTensor (K := K) a b c))
          (i.2, i₀) (i₀, i.1) j = if i = j then 1 else 0 := by
      intro i j
      simp [Tensor.cyclic, matrixMultiplicationTensor, Prod.ext_iff, eq_comm, and_comm]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      h.cyclic.cyclic.card_le_of_identity (fun i : Fin b × Fin c => (i.2, i₀))
        (fun i => (i₀, i.1)) id hminor
  have hca : c * a ≤ R := by
    have hminor : ∀ i j : Fin c × Fin a,
        matrixMultiplicationTensor (K := K) a b c
          (i.2, j₀) (j₀, i.1) j = if i = j then 1 else 0 := by
      intro i j
      simp [matrixMultiplicationTensor, Prod.ext_iff, eq_comm, and_comm]
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      h.card_le_of_identity (fun i : Fin c × Fin a => (i.2, j₀))
        (fun i => (j₀, i.1)) id hminor
  exact ⟨hab, hbc, hca⟩

end BlockIdentities.Square
