module

public import Jrlean.Coc.VarConversions
public import Jrlean.Coc.VarDec
public import Jrlean.Coc.VarInc
public import Jrlean.Coc.Shadows
public import Jrlean.Coc.Shadowed

import Jrlean.Coc.VarIncLemmas
import Jrlean.Coc.ShadowsLemmas
import Jrlean.Coc.ShadowedLemmas

namespace Jrlean.Coc.Var

public section

variable {varKind : VarKind}
variable {x y z : Var'}

attribute [local grind] dec shadows NamedVar inc

-- de Bruijn
@[grind _=_, simp]
theorem dec_eq_pred {x : @Var .deBruijn} : x- = x.pred := rfl

-- Named
@[grind _=_, simp]
theorem dec_eq_with_pred_depth {x : @Var .named} : x- = ⟨x.name, x.depth.pred⟩ := rfl

-- Equality to self
@[simp]
theorem dec_eq_iff : x- = x ↔ x.Unshadowed := by
  cases varKind
  · rw [dec]
    simp only [toNat, Nat.pred_eq_sub_one, unshadowed_iff_eq_zero]
    let x : Nat := x
    show x - 1 = x ↔ x = 0
    omega
  · obtain ⟨n, d⟩ := x
    simp only [dec_eq_with_pred_depth, Nat.pred_eq_sub_one, unshadowed_iff_depth_eq_zero]
    grind only
grind_pattern dec_eq_iff => x-
theorem dec_neq (h : x.Shadowed) : x- ≠ x := by
  grind only [= not_shadowed_iff_unshadowed, usr dec_eq_iff]

@[grind =, simp]
theorem dec_inj (h_x : x.Shadowed) (h_y : y.Shadowed) : x- = y- ↔ x = y := by
  cases varKind
  · simp only [dec_eq_pred, Nat.pred_eq_sub_one]
    grind only [= shadowed_iff_zero_lt]
  · obtain ⟨xName, xDepth⟩ := x
    obtain ⟨yName, yDepth⟩ := y
    simp_all only [shadowed_iff_zero_lt_depth, dec_eq_with_pred_depth, Nat.pred_eq_sub_one]
    grind only

@[grind =, simp]
theorem dec_inc : (x++)- = x := by
  cases varKind
  · rfl
  · rfl

@[grind =, simp]
theorem inc_dec (h : x.Shadowed) : (x-)++ = x := by
  cases varKind
  · simp only [shadowed_iff_zero_lt, toNat] at h
    show (x.toNat - 1) + 1 = x.toNat
    rw [toNat]
    omega
  · obtain ⟨n, d⟩ := x
    simp_all only [shadowed_iff_zero_lt_depth, dec_eq_with_pred_depth, Nat.pred_eq_sub_one]
    grind only [inc]

@[grind →, simp]
theorem shadowed_dec (h : (x-).Shadowed) : x.Shadowed := by
  grind only [=_ not_unshadowed_iff_shadowed, usr dec_eq_iff]

@[grind →, simp]
theorem unshadowed_dec (h : x.Unshadowed) : (x-).Unshadowed := by
  grind only [=_ not_unshadowed_iff_shadowed, usr dec_eq_iff]

@[grind ., simp]
theorem shadows_dec (h : x.Shadowed) : x- < x := by
  suffices x-++ < (x++) by
    grind only [→ neq_of_shadows, = shadows_inc_iff_shadowsEq, = inc_inj, = inc_dec,
      → shadowsEq_right_trans, shadows_inc]
  grind only [= shadows_inc_iff_shadowsEq, = inc_dec]
@[grind ., simp]
theorem shadowsEq_dec : x- ≤ x := by
  grind only [shadows_dec, usr dec_eq_iff, = not_shadowed_iff_unshadowed]
@[grind =, simp]
theorem shadows_dec_iff : x- < x ↔ x.Shadowed := by
  grind only [→ shadowed_of_shadows, shadows_dec]

@[grind =, simp]
theorem shadows_dec_iff_shadowsEq
    (h_x : x.Shadowed)
    : x- < y ↔ x ≤ y := by
  suffices (x-)++ < y++ ↔ x++ ≤ (y++) by
    grind only [shadowsEq_inc_iff_shadows, = shadows_inc_iff_shadowsEq, = inc_inj, = inc_dec, #60ae]
  grind only [shadowsEq_inc_iff_shadows, = shadows_inc_iff_shadowsEq, = inc_inj, = inc_dec, #1e10]
@[grind →, simp]
theorem shadows_dec_to (h : x- < y) : x ≤ y := by
  grind only [= shadows_dec_iff_shadowsEq, usr dec_eq_iff, =_ not_unshadowed_iff_shadowed]

@[grind =>, simp]
theorem shadowsEq_dec_iff_shadows
    (h_y : y.Shadowed)
    : x ≤ y- ↔ x < y := by
  suffices x++ ≤ (y-)++ ↔ x++ < (y++) by
    grind only [shadowsEq_inc_iff_shadows, = shadows_inc_iff_shadowsEq, = inc_inj, = inc_dec, #60ae]
  grind only [= shadows_inc_iff_shadowsEq, = inc_dec]
@[grind →, simp]
theorem shadowsEq_dec_to (h : x ≤ y-) : x ≤ y := by
  grind only [→ shadowed_of_shadows, usr dec_eq_iff, => shadowsEq_dec_iff_shadows, → shadowed_dec,
    =_ not_unshadowed_iff_shadowed]

@[grind =, simp]
theorem shadows_dec_dec (h : x.Shadowed) : x- < y- ↔ x < y := by
  simp
  grind only [→ shadowed_of_shadows, → shadowsEq_dec_to, usr dec_eq_iff,
    =_ not_unshadowed_iff_shadowed, → shadowsEq_trans, => shadowsEq_dec_iff_shadows,
    shadowsEq_antisymm, shadowsEq_dec, #dadb]
@[grind =, simp]
theorem shadowsEq_dec_dec (h_x : x.Shadowed) (h_y : y.Shadowed) : x- ≤ y- ↔ x ≤ y := by
  grind only [= shadows_dec_dec, = dec_inj, #15ca]
@[grind =, simp]
theorem shadowsEq_dec_dec' (h_x : x.Unshadowed) (h_y : y.Shadowed) : x- ≤ y- ↔ x < y := by
  grind only [=> shadowsEq_dec_iff_shadows, usr dec_eq_iff]
