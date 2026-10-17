/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! Integer arithmetic for the manuscript's interpolation separator.
This is finite infrastructure, not the tensor separator theorem. -/
@[expose] public section
namespace BlockIdentities.Square

/-- Zero-based forms of the three interpolation exponents. -/
def separatorFilterDegree {M : ℕ} (g h u v : Fin M) : ℕ :=
  2 * g.val + (u.val + (M - 1) - h.val) + (2 * (M - 1) - v.val - h.val)

theorem separatorFilterDegree_le {M : ℕ} (g h u v : Fin M) :
    separatorFilterDegree g h u v ≤ 6 * (M - 1) := by
  have hg := g.isLt
  have hh := h.isLt
  have hu := u.isLt
  have hv := v.isLt
  unfold separatorFilterDegree
  omega

theorem separatorFilterDegree_eq_iff {M : ℕ} (g h u v : Fin M) :
    separatorFilterDegree g h u v = 3 * (M - 1) ↔
      2 * ((g.val : ℤ) - (h.val : ℤ)) + (u.val : ℤ) - (v.val : ℤ) = 0 := by
  have hg := g.isLt
  have hh := h.isLt
  have hu := u.isLt
  have hv := v.isLt
  unfold separatorFilterDegree
  omega

/-- Nonnegative shifted polynomial weights, retaining zero-based indices. -/
def separatorFirstWeight {M : ℕ} (g : Fin M) : ℕ := g.val ^ 2

def separatorSecondWeight {M : ℕ} (h u : Fin M) : ℕ :=
  h.val * u.val + M ^ 2 - h.val ^ 2

def separatorThirdWeight {M : ℕ} (h v : Fin M) : ℕ := M ^ 2 - h.val * v.val

private theorem square_bound {M : ℕ} (h : Fin M) : h.val ^ 2 ≤ M ^ 2 := by
  simpa only [pow_two] using Nat.mul_le_mul h.isLt.le h.isLt.le

private theorem product_bound {M : ℕ} (h v : Fin M) : h.val * v.val ≤ M ^ 2 := by
  simpa only [pow_two] using Nat.mul_le_mul h.isLt.le v.isLt.le

/-- On the interpolation filter the shifted weight is precisely a square
above the common leading degree. All arithmetic here is over integers. -/
theorem separator_weight_identity {M : ℕ} (g h u v : Fin M)
    (hfilter : 2 * ((g.val : ℤ) - (h.val : ℤ)) + (u.val : ℤ) - (v.val : ℤ) = 0) :
    ((separatorFirstWeight g + separatorSecondWeight h u + separatorThirdWeight h v : ℕ) : ℤ) =
      2 * (M : ℤ) ^ 2 + ((g.val : ℤ) - (h.val : ℤ)) ^ 2 := by
  have hy : h.val ^ 2 ≤ h.val * u.val + M ^ 2 := by
    have := square_bound h
    omega
  have hz := product_bound h v
  simp only [separatorFirstWeight, separatorSecondWeight, separatorThirdWeight,
    Nat.cast_add, Nat.cast_sub hy, Nat.cast_sub hz, Nat.cast_mul, Nat.cast_pow]
  have hc := congrArg (fun x : ℤ => x * (h.val : ℤ)) hfilter
  nlinarith [hc]

theorem separator_weight_ge {M : ℕ} (g h u v : Fin M)
    (hfilter : 2 * ((g.val : ℤ) - (h.val : ℤ)) + (u.val : ℤ) - (v.val : ℤ) = 0) :
    2 * M ^ 2 ≤ separatorFirstWeight g + separatorSecondWeight h u + separatorThirdWeight h v := by
  have hid := separator_weight_identity g h u v hfilter
  have hi : (2 : ℤ) * (M : ℤ) ^ 2 ≤
      ((separatorFirstWeight g + separatorSecondWeight h u + separatorThirdWeight h v : ℕ) : ℤ) := by
    nlinarith [sq_nonneg ((g.val : ℤ) - (h.val : ℤ))]
  exact_mod_cast hi

theorem separator_weight_eq_iff {M : ℕ} (g h u v : Fin M)
    (hfilter : 2 * ((g.val : ℤ) - (h.val : ℤ)) + (u.val : ℤ) - (v.val : ℤ) = 0) :
    separatorFirstWeight g + separatorSecondWeight h u + separatorThirdWeight h v =
      2 * M ^ 2 ↔ g = h ∧ u = v := by
  have hid := separator_weight_identity g h u v hfilter
  constructor
  · intro heq
    have heq' :
        ((separatorFirstWeight g + separatorSecondWeight h u + separatorThirdWeight h v : ℕ) : ℤ) =
          2 * (M : ℤ) ^ 2 := by exact_mod_cast heq
    have hsquare : ((g.val : ℤ) - (h.val : ℤ)) ^ 2 = 0 := by linarith
    have hgh : (g.val : ℤ) = (h.val : ℤ) := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    have huv : (u.val : ℤ) = (v.val : ℤ) := by omega
    exact ⟨Fin.ext (by exact_mod_cast hgh), Fin.ext (by exact_mod_cast huv)⟩
  · rintro ⟨hgh, huv⟩
    subst g
    subst v
    have heq' :
        ((separatorFirstWeight h + separatorSecondWeight h u + separatorThirdWeight h u : ℕ) : ℤ) =
          2 * (M : ℤ) ^ 2 := by simpa using hid
    exact_mod_cast heq'

end BlockIdentities.Square
