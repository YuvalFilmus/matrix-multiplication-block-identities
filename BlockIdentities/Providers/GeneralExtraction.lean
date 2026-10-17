/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.ExtractionFiniteValue
public import BlockIdentities.Square.ExtractionLogLimit

/-! The general extraction principle from actual finite values and rate limits. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Providers
open BlockIdentities BlockIdentities.Square BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open scoped BigOperators

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
by
  classical
  let ρ : Set.Icc (2 : ℝ) 3 := ⟨formalOmega K, formalOmega_mem_Icc (F := K)⟩
  let e := Fintype.equivFin ι
  let G : ι → ℕ → NonzeroTensor K := fun i j =>
    (((B i).permute (π i j)).symmetrize).power (m i j)
  have hG (i : ι) (j : ℕ) :
      cycleClass (tensorClass (G i j).val) = tensorClass (G i j).val :=
    power_cycleClass_fixed (symmetrize_cycleClass_fixed _) _
  have hGval (i : ι) (j : ℕ) :
      valueAtOmega (G i j) = valueAtOmega (B i) ^ (3 * m i j) := by
    change value ρ ((((B i).permute (π i j)).symmetrize).power (m i j)) =
      value ρ (B i) ^ (3 * m i j)
    rw [value_power_nat ρ _ _, value_symmetrize ρ _, value_permute ρ _ _, ← pow_mul]
  have hfinite (j : ℕ) :
      (h j : ℝ) * (b j : ℝ) ^ formalOmega K *
        ∏ i, valueAtOmega (B i) ^ (3 * m i j) ≤
      (u j : ℝ) ^ formalOmega K * valueAtOmega A ^ (3 * n j) *
        (a j : ℝ) ^ formalOmega K := by
    let L : List (NonzeroTensor K) := List.ofFn (fun l : Fin (Fintype.card ι) => G (e.symm l) j)
    have hL : ∀ C ∈ L, cycleClass (tensorClass C.val) = tensorClass C.val := by
      intro C hC
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hC
      exact hG _ _
    have hc : AsymptoticallyRestricts
        (copies (u j) (product (power (symmetrize A.val) (n j)) (square (a j))))
        (copies (h j) (product (square (b j)) (NonzeroTensor.tensorProductList L).val)) := by
      simpa only [NonzeroTensor.tensorProductList, L, List.map_ofFn,
        Function.comp_apply, Function.comp_def, G, e, NonzeroTensor.power, NonzeroTensor.symmetrize, NonzeroTensor.permute]
        using hconvert j
    have hv := extraction_finite_value_bound A L hL (n j) (a j) (b j) (u j) (h j)
      (hn j) (ha j) (hb j) (hu j) (hh j) hc
    have hp : (L.map valueAtOmega).prod = ∏ i, valueAtOmega (B i) ^ (3 * m i j) := by
      calc
        (L.map valueAtOmega).prod = ∏ l : Fin (Fintype.card ι), valueAtOmega (G (e.symm l) j) := by
          simp only [L, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
        _ = ∏ l : Fin (Fintype.card ι), valueAtOmega (B (e.symm l)) ^ (3 * m (e.symm l) j) := by
          apply Finset.prod_congr rfl
          intro l _
          exact hGval _ _
        _ = _ := e.symm.prod_comp (fun i : ι => valueAtOmega (B i) ^ (3 * m i j))
    rw [hp] at hv
    exact hv
  exact extraction_log_limit (valueAtOmega A) (fun i => valueAtOmega (B i))
    (one_le_value A ρ) (fun i => one_le_value (B i) ρ)
    (formalOmega K) n a b u h m hn ha hb hu hh hfinite p α β
    hu_rate hm_rate hh_rate hab_rate

end BlockIdentities.Providers
