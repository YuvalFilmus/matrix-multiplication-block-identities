/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Tensor.CyclicValueWitness
public import BlockIdentities.Tensor.CyclicSubrank
public import BlockIdentities.Tensor.MatrixRateAbsorption
public import BlockIdentities.Square.ValueRateLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Strict-loss matrix rates give actual ordinary-value lower bounds. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Square
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
open Filter
open scoped Topology
variable {K : Type*} [Field K]

/-- Absorb source copies at a strictly smaller matrix rate, then pass actual
finite square-output witnesses to the ordinary-value supremum. -/
theorem matrixRate_strict_loss_le_value [IsAlgClosed K]
    (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K)
    (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    (hrank : ¬ Tensor.RankAtMost A.val.coeff 1)
    {r : ℝ} (hRate : MatrixRate A.val r)
    (θ s : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs : 1 ≤ s) (hmargin : Real.log s < θ * Real.log r) :
    s ^ (ρ : ℝ) ≤ value ρ A := by
  have hbinary := cyclic_cube_supplies_two A.property hcycle hrank
  have he := hRate.absorb_copies A.property 3 hbinary θ s hθ0 hθ1 hs hmargin
  have hle : ∀ᶠ n : ℕ in atTop,
      (((Nat.floor (s ^ n) ^ 3 : ℕ) : ℝ) ^ (ρ : ℝ)) ^
        (1 / (3 * (n : ℝ))) ≤ value ρ A := by
    filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
    exact cyclic_square_output_le_value ρ A hcycle hnpos
      (one_le_natFloor_pow s hs n) hn
  exact le_of_tendsto_of_tendsto
    (tendsto_matrixValueGain_natFloor_pow s hs (ρ : ℝ)) tendsto_const_nhds hle

/-- Every matrix-dimension rate of a cyclic non-rank-one tensor gives its
ordinary-value lower bound, including the endpoint rate. -/
theorem matrixRate_rpow_le_value [IsAlgClosed K]
    (ρ : Set.Icc (2 : ℝ) 3) (A : NonzeroTensor K)
    (hcycle : cycleClass (tensorClass A.val) = tensorClass A.val)
    (hrank : ¬ Tensor.RankAtMost A.val.coeff 1)
    {r : ℝ} (hRate : MatrixRate A.val r) :
    r ^ (ρ : ℝ) ≤ value ρ A := by
  have hr : 1 ≤ r := hRate.1
  by_cases heq : r = 1
  · simpa only [heq, Real.one_rpow] using one_le_value A ρ
  have hrgt : 1 < r := lt_of_le_of_ne hr (Ne.symm heq)
  have hlog : 0 < Real.log r := Real.log_pos hrgt
  have hlim : Tendsto (fun s : ℝ => s ^ (ρ : ℝ)) (𝓝[Set.Iio r] r)
      (𝓝 (r ^ (ρ : ℝ))) :=
    (Real.continuousAt_rpow_const r (ρ : ℝ)
      (Or.inl (ne_of_gt (lt_trans zero_lt_one hrgt)))).tendsto.mono_left
        nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  have hnear : ∀ᶠ s : ℝ in 𝓝[Set.Iio r] r, 1 < s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hrgt)
  filter_upwards [self_mem_nhdsWithin, hnear] with s hsr hs
  have hratio : Real.log s / Real.log r < 1 := by
    apply (div_lt_one hlog).2
    exact Real.log_lt_log (lt_trans zero_lt_one hs) hsr
  obtain ⟨θ, hθlo, hθhi⟩ := exists_between
    (show max 0 (Real.log s / Real.log r) < 1 from max_lt zero_lt_one hratio)
  have hθpos : 0 < θ := lt_of_le_of_lt (le_max_left _ _) hθlo
  have hmargin : Real.log s < θ * Real.log r :=
    (div_lt_iff₀ hlog).1 (lt_of_le_of_lt (le_max_right _ _) hθlo)
  exact matrixRate_strict_loss_le_value ρ A hcycle hrank hRate
    θ s hθpos hθhi hs.le hmargin

end BlockIdentities.Square
