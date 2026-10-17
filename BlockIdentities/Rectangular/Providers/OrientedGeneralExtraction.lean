/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ExtractionFiniteValue
public import BlockIdentities.Rectangular.ExtractionLogLimits

@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular.Providers
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
by
  classical
  let e := Fintype.equivFin ι
  let G : ι → ℕ → TensorOf F := fun i j => (B i).power (m i j)
  let L : ℕ → List (TensorOf F) := fun j =>
    List.ofFn (fun l : Fin (Fintype.card ι) => G (e.symm l) j)
  have hfinite (j : ℕ) :
      (h j : ℝ) * matrixWeight S (E j) * ∏ i, orientedValue S (B i) ^ m i j ≤
        (u j : ℝ) ^ (∑ i, S.weight i) * orientedValue S A ^ n j * matrixWeight S (D j) := by
    have hc : AsymptoticallyRestricts
        (copies (u j) (product (power A.val (n j)) (D j).tensor))
        (copies (h j) (product (NonzeroTensor.tensorProductList (L j)).val (E j).tensor)) := by
      simpa only [NonzeroTensor.tensorProductList, L, List.map_ofFn,
        Function.comp_apply, Function.comp_def, G, e, NonzeroTensor.power] using hconvert j
    have hv := ordered_extraction_finite_value_bound S A (L j) (D j) (E j)
      (n j) (u j) (h j) (hu j) (hh j) hc
    have hp : ((L j).map (orientedValue S)).prod = ∏ i, orientedValue S (B i) ^ m i j := by
      calc
        ((L j).map (orientedValue S)).prod =
            ∏ l : Fin (Fintype.card ι), orientedValue S (G (e.symm l) j) := by
          simp only [L, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
        _ = ∏ l : Fin (Fintype.card ι), orientedValue S (B (e.symm l)) ^ m (e.symm l) j := by
          apply Finset.prod_congr rfl
          intro l _
          exact orientedValue_power S _ _
        _ = _ := e.symm.prod_comp (fun i : ι => orientedValue S (B i) ^ m i j)
    rw [hp] at hv
    exact hv
  have hw : Filter.Tendsto (fun j =>
      (Real.log (matrixWeight S (E j)) - Real.log (matrixWeight S (D j))) / (n j : ℝ))
      Filter.atTop (nhds (∑ i, S.weight i * β i)) := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => (hdim_rate i).const_mul (S.weight i))
    apply ht.congr
    intro j
    rw [log_matrixWeight, log_matrixWeight, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ordered_extraction_log_limit (orientedValue S A) (fun i => orientedValue S (B i))
    (lt_of_lt_of_le zero_lt_one (one_le_orientedValue S A))
    (fun i => lt_of_lt_of_le zero_lt_one (one_le_orientedValue S (B i)))
    (∑ i, S.weight i) (fun j => matrixWeight S (D j)) (fun j => matrixWeight S (E j))
    (fun j => matrixWeight_pos S (D j)) (fun j => matrixWeight_pos S (E j))
    n u h m hn hu hh hfinite q α (∑ i, S.weight i * β i) hu_rate hm_rate hh_rate hw

end BlockIdentities.Rectangular.Providers
