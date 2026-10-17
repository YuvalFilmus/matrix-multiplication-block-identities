/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import BlockIdentities.Rectangular.ProfileRealLaws

/-! Genuine density transfer of powered concavity to the positive real quadrant. -/
@[expose] public section
noncomputable section
namespace BlockIdentities.Rectangular

/-- Powered concavity transfers from rational convex combinations. Positive
weights are parameterized by u/(u+v), so density never crosses the domain. -/
theorem continuous_profile_powered_concave
    (f : ℕ+ → ℕ+ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : ({x : ℝ // 0 < x} × {x : ℝ // 0 < x}) → ℝ) (hg : Continuous g)
    (hag : ∀ r s : {x : ℚ // 0 < x},
      g (⟨(r.val : ℝ), by exact_mod_cast r.property⟩,
        ⟨(s.val : ℝ), by exact_mod_cast s.property⟩) = rationalProfile f r s)
    (hconc : ∀ (r s₁ s₂ : {x : ℚ // 0 < x}) (t : ℚ), t ∈ Set.Icc 0 1 →
      ∀ (s₃ : {x : ℚ // 0 < x}), s₃.val = t*s₁.val+(1-t)*s₂.val →
      t * rationalProfile f r s₁ ^ ρ + (1-t) * rationalProfile f r s₂ ^ ρ ≤
        rationalProfile f r s₃ ^ ρ)
    (r s₁ s₂ : {x : ℝ // 0 < x}) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (s₃ : {x : ℝ // 0 < x}) (hmix : s₃.val = t*s₁.val+(1-t)*s₂.val) :
    t*g (r,s₁)^ρ+(1-t)*g (r,s₂)^ρ ≤ g (r,s₃)^ρ := by
  have hc : Continuous (fun x : ℝ => x ^ ρ) := Real.continuous_rpow_const hρ
  have hpos (r a b u v : {x : ℝ // 0 < x}) :
      u.val/(u.val+v.val)*g (r,a)^ρ + v.val/(u.val+v.val)*g (r,b)^ρ ≤
        g (r, ⟨(u.val*a.val+v.val*b.val)/(u.val+v.val),
        div_pos (add_pos (mul_pos u.property a.property) (mul_pos v.property b.property))
          (add_pos u.property v.property)⟩)^ρ := by
    let e := fun q : {x : ℚ // 0 < x} =>
      (⟨(q.val : ℝ), by exact_mod_cast q.property⟩ : {x : ℝ // 0 < x})
    have hd : DenseRange e := positive_rat_cast_dense
    let P := fun z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} ×
        {x : ℝ // 0 < x} × {x : ℝ // 0 < x} × {x : ℝ // 0 < x} =>
      z.2.2.2.1.val/(z.2.2.2.1.val+z.2.2.2.2.val)*g (z.1,z.2.1)^ρ +
      z.2.2.2.2.val/(z.2.2.2.1.val+z.2.2.2.2.val)*g (z.1,z.2.2.1)^ρ ≤
      g (z.1, ⟨(z.2.2.2.1.val*z.2.1.val+z.2.2.2.2.val*z.2.2.1.val)/
        (z.2.2.2.1.val+z.2.2.2.2.val),
        div_pos (add_pos (mul_pos z.2.2.2.1.property z.2.1.property)
          (mul_pos z.2.2.2.2.property z.2.2.1.property))
          (add_pos z.2.2.2.1.property z.2.2.2.2.property)⟩)^ρ
    apply (hd.prodMap (hd.prodMap (hd.prodMap (hd.prodMap hd)))).induction_on
      (p := P) (r,a,b,u,v) _ _
    · have hnz (z : {x : ℝ // 0 < x} × {x : ℝ // 0 < x} ×
          {x : ℝ // 0 < x} × {x : ℝ // 0 < x} × {x : ℝ // 0 < x}) :
          z.2.2.2.1.val+z.2.2.2.2.val ≠ 0 :=
        (add_pos z.2.2.2.1.property z.2.2.2.2.property).ne'
      exact isClosed_le (by fun_prop (disch := first | exact hnz _ | positivity))
        (by fun_prop (disch := first | exact hnz _ | positivity))
    · rintro ⟨r,a,b,u,v⟩
      let tq : ℚ := u.val/(u.val+v.val)
      have hden : 0 < u.val+v.val := add_pos u.property v.property
      have htq : tq ∈ Set.Icc 0 1 := ⟨div_nonneg u.property.le hden.le,
        (div_le_one hden).mpr (le_add_of_nonneg_right v.property.le)⟩
      let sq : {x : ℚ // 0 < x} :=
        ⟨(u.val*a.val+v.val*b.val)/(u.val+v.val),
        div_pos (add_pos (mul_pos u.property a.property) (mul_pos v.property b.property))
          (add_pos u.property v.property)⟩
      have hs : sq.val = tq*a.val+(1-tq)*b.val := by
        dsimp only [sq,tq]; field_simp; ring
      have hh := hconc r a b tq htq sq hs
      have ha := hag r a
      have hb := hag r b
      have hs' := hag r sq
      simp only [sq, Rat.cast_div, Rat.cast_add, Rat.cast_mul] at hs'
      change _ ≤ _ at hh
      dsimp only [P, e, Prod.map]
      rw [ha,hb,hs']
      have htcast : (tq : ℝ) = (u.val : ℝ)/((u.val : ℝ)+(v.val : ℝ)) := by
        simp only [tq, Rat.cast_div, Rat.cast_add]
      have hvcast : 1-(tq : ℝ) = (v.val : ℝ)/((u.val : ℝ)+(v.val : ℝ)) := by
        rw [htcast]
        have hz : (u.val : ℝ)+(v.val : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
        field_simp
        ring
      rw [hvcast, htcast] at hh
      simpa only [sq] using hh
  by_cases ht0 : t = 0
  · have hs : s₃ = s₂ := Subtype.ext (by simpa only [ht0,zero_mul,sub_zero,one_mul,zero_add] using hmix)
    subst s₃
    simp only [ht0,zero_mul,sub_zero,one_mul,zero_add,le_refl]
  by_cases ht1 : t = 1
  · have hs : s₃ = s₁ := Subtype.ext (by simpa only [ht1,one_mul,sub_self,zero_mul,add_zero] using hmix)
    subst s₃
    simp only [ht1,one_mul,sub_self,zero_mul,add_zero,le_refl]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hcomp : 0 < 1-t := sub_pos.mpr htlt
  have hh := hpos r s₁ s₂ ⟨t,htpos⟩ ⟨1-t,hcomp⟩
  have hsum : t+(1-t)=1 := by ring
  have hs : (⟨(t*s₁.val+(1-t)*s₂.val)/(t+(1-t)),
      div_pos (add_pos (mul_pos htpos s₁.property) (mul_pos hcomp s₂.property))
        (add_pos htpos hcomp)⟩ : {x : ℝ // 0 < x}) = s₃ := by
    apply Subtype.ext
    simpa only [hsum, div_one] using hmix.symm
  rw [hs] at hh
  simpa only [hsum,div_one] using hh

end BlockIdentities.Rectangular
