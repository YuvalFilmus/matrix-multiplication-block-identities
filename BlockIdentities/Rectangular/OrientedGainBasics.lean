/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.OrientedWeights
public import BlockIdentities.Tensor.FiniteAsymptoticConversion
public import BlockIdentities.Tensor.ScalarSupply

/-! Elementary witnesses and positivity for the literal oriented gain set. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open OAI.MatrixMultiplication.AuxiliarySeparation.TensorSemiring
variable {F : Type*} [Field F]

theorem orientedGain_pos (S : InteriorSupport F) (T : TensorOf F)
    {v : ℝ} (hv : v ∈ orientedGains S T) : 0 < v := by
  obtain ⟨n, h, hn, hh, D, E, _, rfl⟩ := hv
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh))
    (matrixWeight_pos S E)) (matrixWeight_pos S D)

theorem one_mem_orientedGains (S : InteriorSupport F) (T : TensorOf F) :
    (1 : ℝ) ∈ orientedGains S T := by
  have hc : ClassDegenerates
      (tensorClass (product (power T.val 1) scalarShape.tensor))
      (tensorClass (copies 1 scalarShape.tensor)) := by
    simpa only [tensorClass_product_eq, tensorClass_power_eq, pow_one,
      tensorClass_copies_eq, Nat.cast_one, one_mul,
      show tensorClass (scalarShape.tensor (K := AlgebraicClosure F)) = 1 from matrixClass_one,
      mul_one] using nonzero_scalar_recovery T.property
  refine ⟨1, 1, le_rfl, le_rfl, scalarShape, scalarShape,
    asymptoticallyRestricts_of_classDegenerates hc, ?_⟩
  simp [matrixWeight_scalar]

theorem orientedGains_nonempty (S : InteriorSupport F) (T : TensorOf F) :
    (orientedGains S T).Nonempty := ⟨1, one_mem_orientedGains S T⟩

end BlockIdentities.Rectangular
