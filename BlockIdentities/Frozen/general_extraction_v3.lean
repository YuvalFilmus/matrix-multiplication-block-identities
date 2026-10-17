module
public import BlockIdentities.Providers.GeneralExtraction
public import BlockIdentities.Arithmetic.FormalPolynomial
public import BlockIdentities.Tensor.Value
public import BlockIdentities.Tensor.ConvolutionSplittings
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators
open OAI.MatrixMultiplication
open BlockIdentities BlockIdentities.Square BlockIdentities.Arithmetic

@[expose] public section
namespace BlockIdentities.Square

theorem general_extraction
{K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι]
    (A : NonzeroTensor K) (B : ι → NonzeroTensor K)
    (n a b u h : ℕ → ℕ) (m : ι → ℕ → ℕ)
    (π : ι → ℕ → LegPermutation)
    (hn : ∀ j, 1 ≤ n j) (ha : ∀ j, 1 ≤ a j)
    (hb : ∀ j, 1 ≤ b j) (hu : ∀ j, 1 ≤ u j) (hh : ∀ j, 1 ≤ h j)
    (hn_tendsto : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hconvert : ∀ j, AsymptoticallyRestricts
      (copies (u j) (product (power (symmetrize A.val) (n j)) (square (a j))))
      (copies (h j) (product (square (b j))
        (tensorProductList (List.ofFn (fun l : Fin (Fintype.card ι) =>
          let i := (Fintype.equivFin ι).symm l
          power (symmetrize (permute (K := K) (π i j) (B i).val)) (m i j)))))))
    (p : ι → ℝ) (α β : ℝ)
    (hu_rate : Filter.Tendsto (fun j => Real.log (u j : ℝ) / (n j : ℝ))
      Filter.atTop (nhds 0))
    (hm_rate : ∀ i, Filter.Tendsto (fun j => (m i j : ℝ) / (n j : ℝ))
      Filter.atTop (nhds (p i)))
    (hh_rate : Filter.Tendsto (fun j => Real.log (h j : ℝ) / (3 * (n j : ℝ)))
      Filter.atTop (nhds α))
    (hab_rate : Filter.Tendsto
      (fun j => Real.log ((b j : ℝ) / (a j : ℝ)) / (3 * (n j : ℝ)))
      Filter.atTop (nhds β))
    : Real.log (valueAtOmega A) ≥
        (∑ i, p i * Real.log (valueAtOmega (B i))) + α + formalOmega K * β :=
-- BEGIN APPROVED PROOF REGION
by
  exact BlockIdentities.Providers.general_extraction A B n a b u h m π hn ha hb hu hh
    hn_tendsto hconvert p α β hu_rate hm_rate hh_rate hab_rate
-- END APPROVED PROOF REGION

end BlockIdentities.Square
