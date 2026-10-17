/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.Definitions
public import BlockIdentities.Rectangular.Providers.OrientedGeneralExtraction

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal

theorem oriented_general_extraction {F : Type*} [Field F]
    {ι : Type} [Fintype ι] (S : InteriorSupport F)
    (A : TensorOf F) (B : ι → TensorOf F)
    (n u h : ℕ → ℕ) (m : ι → ℕ → ℕ) (D E : ℕ → MatrixShape)
    (hn : ∀ j, 1 ≤ n j) (hu : ∀ j, 1 ≤ u j) (hh : ∀ j, 1 ≤ h j)
    (hntop : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hconvert : ∀ j, AsymptoticallyRestricts
      (copies (u j) (product (power A.val (n j)) (D j).tensor))
      (copies (h j) (product
        (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
          let i := (Fintype.equivFin ι).symm l
          power (B i).val (m i j)))) (E j).tensor)))
    (q : ι → ℝ) (α : ℝ) (β : Axis → ℝ)
    (hu_rate : Filter.Tendsto (fun j => Real.log (u j : ℝ) / (n j : ℝ))
      Filter.atTop (nhds 0))
    (hm_rate : ∀ i, Filter.Tendsto (fun j => (m i j : ℝ) / (n j : ℝ))
      Filter.atTop (nhds (q i)))
    (hh_rate : Filter.Tendsto (fun j => Real.log (h j : ℝ) / (n j : ℝ))
      Filter.atTop (nhds α))
    (hdim_rate : ∀ i, Filter.Tendsto
      (fun j => (logDotDimensions (E j) i - logDotDimensions (D j) i) / (n j : ℝ))
      Filter.atTop (nhds (β i))) :
  Real.log (orientedValue S A) ≥
      (∑ i, q i * Real.log (orientedValue S (B i))) + α + ∑ i, S.weight i * β i :=
-- BEGIN APPROVED PROOF REGION
by
  exact Providers.oriented_general_extraction S A B n u h m D E hn hu hh hntop
    hconvert q α β hu_rate hm_rate hh_rate hdim_rate
-- END APPROVED PROOF REGION

end BlockIdentities.Rectangular
