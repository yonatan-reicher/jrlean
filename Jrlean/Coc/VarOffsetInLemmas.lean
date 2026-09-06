module

public import Jrlean.Coc.VarOffseting
public import Jrlean.Coc.Shadowed

import Jrlean.Coc.ShadowedLemmas
import Jrlean.Coc.ShadowsLemmas
import Jrlean.Coc.VarIncLemmas
import Jrlean.Coc.VarDecLemmas

namespace Jrlean.Coc.Var

public section

variable {varKind : VarKind}
variable {x y z : Var'}

@[grind =]
theorem offsetIn_eq : x↑y = if y ≤ x then x++ else x := rfl
@[grind =, simp]
theorem offsetIn_of_shadowsEq (h : y ≤ x) : x↑y = x++ := by grind only [= offsetIn_eq]
@[grind =]
theorem offsetIn_eq_inc_iff : x↑y = x++ ↔ y ≤ x := by
  grind only [= offsetIn_of_shadowsEq, = offsetIn_eq, inc_neq, #d0c7]
@[grind =, simp]
theorem offsetIn_of_not_shadowsEq (h : ¬(y ≤ x)) : x↑y = x := by grind only [= offsetIn_eq]
theorem offsetIn_eq_iff : x↑y = x ↔ ¬(y ≤ x) := by
    grind only [= offsetIn_of_not_shadowsEq, = offsetIn_of_shadowsEq, = offsetIn_eq_inc_iff, inc_neq]
grind_pattern offsetIn_eq_iff => x↑y where x =?= x↑y

@[grind ., simp]
theorem shadowsEq_offsetIn : x ≤ x↑y := by
  grind only [= offsetIn_of_not_shadowsEq, = offsetIn_of_shadowsEq, → neq_of_shadows,
    = offsetIn_eq_inc_iff, → shadowsEq_right_trans, shadows_inc, #82de]

@[grind =, simp]
theorem shadows_offsetIn_iff : x < x↑y ↔ y ≤ x := by
  grind only [→ neq_of_shadows, shadowsEq_offsetIn, = offsetIn_of_shadowsEq, = offsetIn_eq,
    = offsetIn_eq_inc_iff, inc_neq, #6985]

@[grind =_, simp]
theorem offsetIn_neq_iff : x↑y ≠ x ↔ x↑y = x++ := by
  grind only [= offsetIn_of_not_shadowsEq, = offsetIn_eq_inc_iff, inc_neq, #3797]
@[grind =, simp]
theorem offsetIn_neq_inc_iff : x↑y ≠ x++ ↔ x↑y = x := by
  grind only [=_ offsetIn_neq_iff]

@[grind =, simp]
theorem inc_offsetIn : (x↑y)++ = (x++)↑(y++) := by
  grind =>
    instantiate only [= inc_inj, = offsetIn_neq_inc_iff, =_ offsetIn_neq_iff, = offsetIn_eq_inc_iff,
      = offsetIn_eq]
    instantiate only [= offsetIn_neq_inc_iff, = offsetIn_eq_inc_iff, shadowsEq_inc_iff_shadows]
    instantiate only [= shadows_inc_iff_shadowsEq]
    cases #c50d
@[grind =, simp]
theorem dec_offsetIn (h_x : x.Shadowed) (h_y : y.Shadowed) : (x↑y)- = (x-)↑(y-) := by
  grind =>
    instantiate only [= dec_inj, = offsetIn_of_shadowsEq, = offsetIn_eq]
    instantiate only [= shadows_dec_iff_shadowsEq, = offsetIn_eq_inc_iff, =_ offsetIn_neq_iff,
      = offsetIn_neq_inc_iff, = inc_dec]
    instantiate only [=> shadowsEq_dec_iff_shadows]
    cases #aa1a
    · instantiate only [= shadowed_iff_zero_lt]
      cases #8c23 <;> instantiate only [= dec_inc]
    · cases #8c23 <;> instantiate only [= dec_inc]
