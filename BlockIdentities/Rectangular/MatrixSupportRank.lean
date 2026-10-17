/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.AsymptoticRankBasics
public import BlockIdentities.Rectangular.OrientedWeights
public import BlockIdentities.Arithmetic.ShapeRankLimits

/-! A supporting weight is bounded by every genuine exact matrix-power rank
root, hence by the literal matrix asymptotic rank. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular
open BlockIdentities.Square
open BlockIdentities.Arithmetic
open OAI.MatrixMultiplication.Foundation
open OAI.MatrixMultiplication.AuxiliarySeparation
open scoped BigOperators NNReal
variable {F : Type*} [Field F]

/-- Undo the actual ofTensor coordinate enumeration before reindexing each word
as one matrix dimension. The rank budget is the genuine exact power rank. -/
theorem matrixShape_power_rankAtMost (D : MatrixShape) (n : ℕ) :
    Tensor.RankAtMost
      (matrixMultiplicationTensor (K := AlgebraicClosure F) (D.a ^ n) (D.b ^ n) (D.c ^ n))
      (exactRank (power (D.tensor (K := AlgebraicClosure F)) n).coeff) := by
  let ex := Fintype.equivFin (Fin D.a × Fin D.b)
  let ey := Fintype.equivFin (Fin D.b × Fin D.c)
  let ez := Fintype.equivFin (Fin D.c × Fin D.a)
  have hcoeff (x : Fin D.a × Fin D.b) (y : Fin D.b × Fin D.c)
      (z : Fin D.c × Fin D.a) :
      (D.tensor (K := AlgebraicClosure F)).coeff (ex x) (ey y) (ez z) =
        matrixMultiplicationTensor D.a D.b D.c x y z := by
    change matrixMultiplicationTensor D.a D.b D.c
      (ex.symm (ex x)) (ey.symm (ey y)) (ez.symm (ez z)) = _
    rw [ex.symm_apply_apply, ey.symm_apply_apply, ez.symm_apply_apply]
  have hr := exactRank_spec (Tensor.power (D.tensor (K := AlgebraicClosure F)).coeff n)
  rw [← exactRank_power_coeff] at hr
  let fx (x : Fin n → Fin D.a × Fin D.b) := fun i => ex (x i)
  let fy (y : Fin n → Fin D.b × Fin D.c) := fun i => ey (y i)
  let fz (z : Fin n → Fin D.c × Fin D.a) := fun i => ez (z i)
  have hp := hr.pullback fx fy fz
  have heq : Tensor.pullback fx fy fz
      (Tensor.power (D.tensor (K := AlgebraicClosure F)).coeff n) =
      Tensor.power (matrixMultiplicationTensor (K := AlgebraicClosure F) D.a D.b D.c) n := by
    funext x y z
    simp only [Tensor.pullback, Tensor.power, fx, fy, fz, hcoeff]
  have hp' : Tensor.RankAtMost
      (Tensor.power (matrixMultiplicationTensor (K := AlgebraicClosure F) D.a D.b D.c) n)
      (exactRank (power (D.tensor (K := AlgebraicClosure F)) n).coeff) :=
    (congrArg (fun Q : Tensor (AlgebraicClosure F)
      (Fin n → Fin D.a × Fin D.b) (Fin n → Fin D.b × Fin D.c)
      (Fin n → Fin D.c × Fin D.a) => Tensor.RankAtMost Q
        (exactRank (power (D.tensor (K := AlgebraicClosure F)) n).coeff)) heq).mp hp
  exact rankAtMost_rectangular_of_tensor_power hp'

/-- The actual support inequality is applied once to the powered matrix shape. -/
theorem matrixWeight_le_exact_power_root (S : InteriorSupport F) (D : MatrixShape)
    (n : ℕ) (hn : 1 ≤ n) :
    matrixWeight S D ≤
      (exactRank (power (D.tensor (K := AlgebraicClosure F)) n).coeff : ℝ) ^ (1 / (n : ℝ)) := by
  let R := exactRank (power (D.tensor (K := AlgebraicClosure F)) n).coeff
  have hpa : 1 ≤ D.a ^ n := by have := pow_pos D.a_pos n; omega
  have hpb : 1 ≤ D.b ^ n := by have := pow_pos D.b_pos n; omega
  have hpc : 1 ≤ D.c ^ n := by have := pow_pos D.c_pos n; omega
  let u : Axis → ℝ≥0 :=
    ![⟨Real.log ((D.c ^ n : ℕ) : ℝ), Real.log_nonneg (by exact_mod_cast hpc)⟩,
      ⟨Real.log ((D.a ^ n : ℕ) : ℝ), Real.log_nonneg (by exact_mod_cast hpa)⟩,
      ⟨Real.log ((D.b ^ n : ℕ) : ℝ), Real.log_nonneg (by exact_mod_cast hpb)⟩]
  have hs := S.supporting u
  have hu (i : Axis) : (u i : ℝ) =
      ![Real.log ((D.c ^ n : ℕ) : ℝ), Real.log ((D.a ^ n : ℕ) : ℝ),
        Real.log ((D.b ^ n : ℕ) : ℝ)] i := by
    fin_cases i <;> rfl
  have hsum : (∑ i, S.weight i * (u i : ℝ)) = (n : ℝ) * Real.log (matrixWeight S D) := by
    simp_rw [hu]
    rw [log_matrixWeight]
    simp [Fin.sum_univ_succ, logDotDimensions, Nat.cast_pow, Real.log_pow]
    ring
  rw [hsum] at hs
  have hbound : orientedExponent F u ≤ Real.log (R : ℝ) :=
    formalShapeOmega_log_dimensions_le_log_rank hpa hpb hpc (matrixShape_power_rankAtMost D n)
  have hlog : (n : ℝ) * Real.log (matrixWeight S D) ≤ Real.log (R : ℝ) := hs.trans hbound
  have hRone := one_le_exactRank_of_nonzero _
    (nonzero_power (nonzero_matrixShape (K := AlgebraicClosure F) D) n)
  have hRpos : 0 < (R : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hRone)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply (Real.log_le_log_iff (matrixWeight_pos S D)
    (Real.rpow_pos_of_pos hRpos _)).mp
  rw [Real.log_rpow hRpos]
  have hh : Real.log (matrixWeight S D) ≤ Real.log (R : ℝ) / (n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hlog)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh

/-- Supporting matrix weights are bounded by the literal asymptotic rank.
There is no comparison of separate supporting lower bounds. -/
theorem matrixWeight_le_tensorAsymptoticRank (S : InteriorSupport F) (D : MatrixShape) :
    matrixWeight S D ≤ tensorAsymptoticRank (D.nonzeroTensor (K := AlgebraicClosure F)) := by
  apply le_csInf (tensorRankRoots_nonempty _)
  rintro r ⟨n, hn, rfl⟩
  exact matrixWeight_le_exact_power_root S D n hn

end BlockIdentities.Rectangular
