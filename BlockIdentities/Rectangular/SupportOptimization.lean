/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedGeometry
public import BlockIdentities.Rectangular.AngularOptimization

/-! Scalar optimization of an actual support objective. The angular premise is
explicit here; the source angular theorem is proved from convolution profiles. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open scoped BigOperators NNReal
variable {F : Type*} [Field F]

/-- A zero support coordinate already supplies the whole angular lower bound. -/
theorem support_angles_ge_of_weight_zero (S : InteriorSupport F) (i : Axis)
    (hi : S.weight i = 0) :
    Real.pi / 2 ≤ ∑ j, Real.arccos (Real.sqrt (S.weight j)) := by
  have h := Finset.single_le_sum
    (f := fun j : Axis => Real.arccos (Real.sqrt (S.weight j)))
    (fun j _ => Real.arccos_nonneg _) (Finset.mem_univ i)
  simpa only [hi, Real.sqrt_zero, Real.arccos_zero] using h

/-- The support objective in matrix argument order (Y,Z,X). -/
theorem support_objective_le_of_angles (S : InteriorSupport F)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hangle : Real.pi / 2 ≤ ∑ i, Real.arccos (Real.sqrt (S.weight i))) :
    a * S.weight 1 + b * S.weight 2 + c * S.weight 0 ≤
      if c ≤ a * b / (a + b) then a + b
      else (a + b + c) / 2 + (a * b / c + a * c / b + b * c / a) / 4 := by
  have hang : Real.pi / 2 ≤ Real.arccos (Real.sqrt (S.weight 1)) +
      Real.arccos (Real.sqrt (S.weight 2)) + Real.arccos (Real.sqrt (S.weight 0)) := by
    have heq : (∑ i, Real.arccos (Real.sqrt (S.weight i))) =
        Real.arccos (Real.sqrt (S.weight 1)) + Real.arccos (Real.sqrt (S.weight 2)) +
          Real.arccos (Real.sqrt (S.weight 0)) := by
      rw [Fin.sum_univ_three]
      change _ + _ + _ = _ + _ + _
      ring
    rwa [heq] at hangle
  split_ifs with hthreshold
  · exact weighted_parameters_le_threshold ha hb hc.le hthreshold
      (interiorSupport_weight_bounds S 1) (interiorSupport_weight_bounds S 2)
      (interiorSupport_weight_bounds S 0) hang
  · exact weighted_parameters_le ha hb hc
      (interiorSupport_weight_bounds S 1) (interiorSupport_weight_bounds S 2)
      (interiorSupport_weight_bounds S 0) hang

end BlockIdentities.Rectangular
