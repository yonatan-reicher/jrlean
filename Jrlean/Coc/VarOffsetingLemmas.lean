module

public import Jrlean.Coc.VarOffseting

import Jrlean.Coc.ShadowsLemmas
import Jrlean.Coc.ShadowedLemmas
import Jrlean.Coc.VarIncLemmas
import Jrlean.Coc.VarDecLemmas

import Jrlean.SetTactic
import Jrlean.ByContra

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}
variable {v v' v'' x y z : Var'}

attribute [local grind .]
  Var.offsetIn
  Var.offsetOut
  Offset.offsetIn
  Offset.offsetOut
  NamedVar.ext

@[grind _=_] private theorem offsetIn_notation : v↑v' = v.offsetIn v' := rfl
@[grind _=_] private theorem offsetOut_notation : v↓v' = v.offsetOut v' := rfl

@[simp]
theorem Var.offsetOut_isSome_of_neq
    (h : v ≠ v')
    : (v↓v').isSome := by
  grind only [= offsetOut_notation, offsetOut, = Option.isSome_some]
grind_pattern Var.offsetOut_isSome_of_neq => v↓v'

@[grind =, simp]
theorem Var.offsetOut_eq_none : v↓v = none := by
  grind only [= offsetOut_notation, offsetOut]

@[grind =, simp]
theorem Var.offsetOut_isSome
    : (v↓v').isSome = (v ≠ v') := by
  grind only [usr offsetOut_isSome_of_neq, = offsetOut_notation, offsetOut, = Option.isSome_none,
    #5af2]

@[simp]
theorem Var.offsetOut_eq_some_of_neq
    (h : v ≠ v')
    : ∃ v'', v↓v' = some v'' := by
  have : (v↓v').isSome := Var.offsetOut_isSome_of_neq h
  exact Option.isSome_iff_exists.mp this
grind_pattern Var.offsetOut_eq_some_of_neq => v↓v'

/-- Offseting in never gives the same variable as the rhs. -/
@[grind ., simp]
theorem Var.offsetIn_neq : v↑v' ≠ v' := by
  if h : v = v' then
    grind only [= offsetIn_notation, offsetIn, → neq_of_shadows, shadows_inc]
  else
    simp only [Offset.offsetIn, offsetIn]
    grind only [shadowsEq_inc_iff_shadows, → neq_of_shadows, #d94a]

@[grind =, simp]
theorem Var.offsetOut_offsetIn : (v↑v')↓v' = some v := by
  grind =>
    instantiate only [usr offsetOut_eq_some_of_neq, = offsetOut_notation, offsetIn_neq,
      = offsetIn_notation]
    instantiate only [offsetOut, offsetIn]
    cases #aa1a
    · instantiate only [= shadows_iff_lt]
      cases #3bc3 <;>
        cases #d94a <;>
          instantiate only [= shadows_inc_iff_shadowsEq] <;> instantiate only [= dec_inc]
    · instantiate only [= shadows_iff_name_eq_and_depth_lt]
      instantiate only [→ not_shadows_of_name_neq]
      instantiate only [→ shadowsEq_right_trans, → shadowsEq_trans]
      cases #3bc3 <;>
        cases #d94a <;> instantiate only [shadows_inc] <;> instantiate only [= dec_inc]

@[grind =, simp]
theorem Var.offsetIn_offsetOut_of_isSome
    (h : (v↓v').isSome)
    : (v↓v').map (·↑v') = some v := by
  if h₁ : v < v' then
    grind only [= offsetOut_isSome, = offsetOut_notation, offsetOut, → shadows_trans,
      = Option.map_some, → neq_of_shadows, = offsetIn_notation, offsetIn]
  else if h₂ : v' < v then
    grind only [= offsetOut_isSome, usr offsetOut_eq_some_of_neq, = offsetOut_notation,
      → shadowed_of_shadows, → neq_of_shadows, offsetOut, =_ not_unshadowed_iff_shadowed,
      = not_shadowed_iff_unshadowed, = Option.map_some, = offsetIn_notation, offsetIn,
      = shadows_iff_lt, = shadowed_iff_zero_lt, => shadowsEq_dec_iff_shadows,
      = unshadowed_iff_eq_zero, = inc_dec, = shadows_iff_name_eq_and_depth_lt, shadowsEq_antisymm,
      = dec_eq_with_pred_depth, = shadows_dec_iff_shadowsEq, NamedVar.ext, #aa1a, #a87d, #f0d2,
      #2864]
  else
    grind only [= offsetOut_isSome, = offsetOut_notation, offsetOut, = Option.map_some,
      = offsetIn_notation, offsetIn]

@[grind =]
theorem Var.offsetIn_offsetOut_eq_ite
    : (v↓v').map (·↑v') = if v = v' then none else some v := by
  grind only [= offsetIn_offsetOut_of_isSome, = offsetOut_notation, = offsetOut_isSome, offsetOut,
    = Option.map_none, #3ced]

@[grind =]
theorem Var.bind_offsetOut_eq_ite
    : (v↓v').bind f = if v = v' then none else f (v↓v').get! := by
  grind =>
    instantiate only [usr offsetOut_eq_some_of_neq]
    cases #8cec
    · instantiate only [= offsetOut_eq_none]
      instantiate only [= Option.bind_none]
    · cases #a87d <;> instantiate only [= Option.bind_some, = Option.get!_some]

@[grind =]
theorem Var.offsetOut_offsetOut_of_isSome
    (h : (x↓y).isSome)
    (h : (y↓z).isSome)
    : (x↓y).get!↓z = (x↓(z↑y)).bind (·↓(y↓z).get!) := by
  simp_all
  grind

@[grind =, simp]
theorem Var.offsetOut_eq_none_iff : v↓v' = none ↔ v = v' := by
  grind =>
    instantiate only [usr offsetOut_isSome_of_neq]
    instantiate only [= offsetOut_isSome]
    cases #5373
    · instantiate only [= Option.isSome_none]
    · instantiate only [= offsetOut_eq_none]

theorem Var.offsetOut_bind_offsetOut : (x↓y).bind (·↓z) = (x↓(z↑y)).bind (·↓(y↑z)) := by
  rw [Var.bind_offsetOut_eq_ite]
  split
  · subst y
    symm
    rw [Option.bind_eq_none_iff]
    intro x' h
    rw [offsetOut_eq_none_iff]
    simp_all
  · sorry

/-- A very obvious theorem, that makes grind case-split when needed. -/
@[grind =]
theorem Var.offsetOut_eq_ite
    : v↓v' = if v = v' then none else some ((v↓v').get!) := by
  grind =>
    instantiate only [usr offsetOut_eq_some_of_neq]
    cases #667f
    · instantiate only [= offsetOut_eq_none]
    · cases #a87d <;> instantiate only [= Option.get!_some]

