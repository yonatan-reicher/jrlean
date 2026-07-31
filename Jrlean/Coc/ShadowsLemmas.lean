module

public import Jrlean.Coc.Shadows
public import Jrlean.Coc.Shadowed

import Jrlean.Coc.ShadowedLemmas
import Jrlean.ByContra

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}
variable {x y z : Var'}

attribute [local grind] shadows VarKind

@[grind →, simp]
theorem neq_of_shadows (h : x < y) : x ≠ y := by grind only [shadows]

@[grind →, simp] theorem shadows_trans (h₁ : x < y) (h₂ : y < z) : x < z := by grind only [shadows]
@[grind →, simp] theorem shadowsEq_trans (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by grind only [shadows]
@[grind →, simp] theorem shadowsEq_left_trans (h₁ : x ≤ y) (h₂ : y < z) : x ≤ z := by grind only [shadows]
@[grind →, simp] theorem shadowsEq_right_trans (h₁ : x < y) (h₂ : y ≤ z) : x ≤ z := by grind only [shadows]
instance : @Trans Var' Var' Var' shadows shadows shadows := ⟨shadows_trans⟩
instance : @Trans Var' Var' Var' shadowsEq shadowsEq shadowsEq := ⟨shadowsEq_trans⟩
instance : @Trans Var' Var' Var' shadowsEq shadows shadowsEq := ⟨shadowsEq_left_trans⟩
instance : @Trans Var' Var' Var' shadows shadowsEq shadowsEq := ⟨shadowsEq_right_trans⟩

@[grind →, simp]
theorem shadowed_of_shadows (h : x < y) : y.Shadowed := by
  by_contra h_unshadowed
  rw [not_shadowed_iff_unshadowed] at h_unshadowed
  cases varKind
  · grind only [→ neq_of_shadows, shadows, =_ not_shadowed_iff_unshadowed, = shadowed_iff_zero_lt]
  · grind only [shadows, = unshadowed_iff_depth_eq_zero]

-- @[grind] <-- Already exists because x ≤ y is an abbreviation!
theorem shadowsEq_iff_shadows_or_eq : x ≤ y ↔ x < y ∨ x = y := by
  grind only

-- @[grind ., simp]
-- theorem shadowsEq_of_shadows (h : x < y) : x ≤ y := by exact Or.intro_left (x = y) h

@[grind =, simp]
theorem shadows_iff_lt {x y : @Var .deBruijn} : x < y ↔ x.toNat < y.toNat := by rw [shadows]
@[grind =, simp]
theorem shadows_iff_name_eq_and_depth_lt {x y : @Var .named}
    : x < y ↔ x.name = y.name ∧ x.depth < y.depth := by rw [shadows]

@[grind →, simp]
theorem not_shadows_of_name_neq {x y : @Var .named} (h : x.name ≠ y.name) : ¬(x < y) := by
  grind only [= shadows_iff_name_eq_and_depth_lt]
