/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BlockIdentities.Square.MatrixRateLimits
public import Mathlib.Tactic.Linarith

/-! Rounded linear scales absorb arbitrary sublinear overhead schedules. -/

@[expose] public section
noncomputable section

namespace BlockIdentities.Square

open Filter
open scoped Topology

theorem floor_linear_tendsto_atTop (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => Nat.floor (θ * (N : ℝ))) atTop atTop :=
  tendsto_nat_floor_mul_atTop θ hθ

theorem floor_linear_div_tendsto (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => (Nat.floor (θ * (N : ℝ)) : ℝ) / (N : ℝ))
      atTop (𝓝 θ) :=
  (tendsto_nat_floor_mul_div_atTop hθ).comp tendsto_natCast_atTop_atTop

/-- Transport an arbitrary rate along floor(θ*N), without monotonicity of the
underlying sequence. The new rate is the old rate multiplied by θ. -/
theorem rate_comp_floor_linear (u : ℕ → ℝ) (L θ : ℝ) (hθ : 0 < θ)
    (hu : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => u (Nat.floor (θ * (N : ℝ))) / (N : ℝ))
      atTop (𝓝 (L * θ)) := by
  have hf := floor_linear_tendsto_atTop θ hθ
  have hratio := floor_linear_div_tendsto θ hθ.le
  have hprod := (hu.comp hf).mul hratio
  apply hprod.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop (1 : ℕ)),
    eventually_ge_atTop (1 : ℕ)] with N hfloor hN
  have hfpos : 0 < (Nat.floor (θ * (N : ℝ)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  change (u (Nat.floor (θ * (N : ℝ))) / (Nat.floor (θ * (N : ℝ)) : ℝ)) *
      ((Nat.floor (θ * (N : ℝ)) : ℝ) / (N : ℝ)) =
    u (Nat.floor (θ * (N : ℝ))) / (N : ℝ)
  field_simp [ne_of_gt hfpos, ne_of_gt hNpos] <;> ring

/-- Every sublinear overhead fits in the unused fraction of the total power
at the rounded scale floor(θ*N), for fixed 0<θ<1 and fixed multiplicity p. -/
theorem eventually_floor_linear_absorption (ℓ : ℕ → ℕ)
    (hℓ : Tendsto (fun n : ℕ => (ℓ n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    (p : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ N : ℕ in atTop,
      Nat.floor (θ * (N : ℝ)) + p * ℓ (Nat.floor (θ * (N : ℝ))) ≤ N := by
  have hsub : Tendsto (fun N : ℕ =>
      (ℓ (Nat.floor (θ * (N : ℝ))) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using rate_comp_floor_linear (fun n => (ℓ n : ℝ)) 0 θ hθ0 hℓ
  have hlim : Tendsto (fun N : ℕ =>
      (Nat.floor (θ * (N : ℝ)) : ℝ) / N +
        (p : ℝ) * ((ℓ (Nat.floor (θ * (N : ℝ))) : ℝ) / N)) atTop (𝓝 θ) := by
    simpa using (floor_linear_div_tendsto θ hθ0.le).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (p : ℝ))
        atTop (𝓝 (p : ℝ))).mul hsub)
  filter_upwards [hlim.eventually_lt_const hθ1, eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNpos)
  have hnum : (Nat.floor (θ * (N : ℝ)) : ℝ) +
      (p : ℝ) * (ℓ (Nat.floor (θ * (N : ℝ))) : ℝ) ≤ N := by
    have hdiv : ((Nat.floor (θ * (N : ℝ)) : ℝ) +
        (p : ℝ) * (ℓ (Nat.floor (θ * (N : ℝ))) : ℝ)) / N ≤ 1 := by
      calc
        _ = (Nat.floor (θ * (N : ℝ)) : ℝ) / N +
            (p : ℝ) * ((ℓ (Nat.floor (θ * (N : ℝ))) : ℝ) / N) := by ring
        _ ≤ 1 := hN.le
    simpa only [one_mul] using (div_le_iff₀ hpos).1 hdiv
  exact_mod_cast hnum

/-- A strict logarithmic margin gives the desired rounded square dimension
after reducing the source scale to floor(θ*N). -/
theorem eventually_natFloor_pow_le_reindexed (r s θ : ℝ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hθ : 0 < θ)
    (hmargin : Real.log s < θ * Real.log r) :
    ∀ᶠ N : ℕ in atTop,
      Nat.floor (s ^ N) ≤ Nat.floor (r ^ Nat.floor (θ * (N : ℝ))) := by
  have hleft := tendsto_log_natFloor_pow_div s hs
  have hright := rate_comp_floor_linear
    (fun n : ℕ => Real.log (Nat.floor (r ^ n) : ℝ)) (Real.log r) θ hθ
    (tendsto_log_natFloor_pow_div r hr)
  have hgap : Real.log s < Real.log r * θ := by simpa only [mul_comm] using hmargin
  filter_upwards [hleft.eventually_lt hright hgap, eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNpos)
  have hspos : 0 < (Nat.floor (s ^ N) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow s hs N))
  have hrpos : 0 < (Nat.floor (r ^ Nat.floor (θ * (N : ℝ))) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_natFloor_pow r hr _))
  have hlogs := (div_lt_div_iff_of_pos_right hpos).1 hN
  have hreal := (Real.log_lt_log_iff hspos hrpos).1 hlogs
  exact_mod_cast hreal.le

end BlockIdentities.Square
