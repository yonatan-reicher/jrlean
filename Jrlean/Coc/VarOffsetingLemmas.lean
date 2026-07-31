module

public import Jrlean.Coc.VarOffseting

import Jrlean.SetTactic

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}
variable {v v' v'' x y z : Var'}

attribute [local grind .]
  Var.offsetIn
  Var.offsetOut
  Var.offsetInDeBruijn
  Var.offsetInNamed
  Var.offsetOutDeBruijn
  Var.offsetOutNamed
  Offset.offsetIn
  Offset.offsetOut
  NamedVar.ext

@[grind _=_] private theorem offsetIn_notation : v↑v' = v.offsetIn v' := rfl
@[grind _=_] private theorem offsetOut_notation : v↓v' = v.offsetOut v' := rfl

@[simp]
theorem Var.offsetOut_isSome_of_neq
    (h : v ≠ v')
    : (v↓v').isSome := by
  grind only [= eq_2, = offsetOut_notation, offsetOut, offsetOutDeBruijn, = Option.isSome_some, offsetOutNamed,
    NamedVar.ext, #aa1a, #616e, #75b3, #9840]
grind_pattern Var.offsetOut_isSome_of_neq => v↓v'

@[grind =, simp]
theorem Var.offsetOut_eq_none : v↓v = none := by
  grind only [= offsetOut_notation, offsetOut, offsetOutDeBruijn, offsetOutNamed, #aa1a]

@[grind =, simp]
theorem Var.offsetOut_isSome
    : (v↓v').isSome = (v ≠ v') := by
  grind only [usr offsetOut_isSome_of_neq, = offsetOut_notation, offsetOut, offsetOutDeBruijn,
    = Option.isSome_none, offsetOutNamed, #5af2, #aa1a]

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
  grind only [= offsetIn_notation, offsetIn, offsetInDeBruijn, offsetInNamed, #aa1a, #0019, #46c1,
    #8585]

@[grind =, simp]
theorem Var.offsetOut_offsetIn : (v↑v')↓v' = some v := by
  set vIn := v↑v' with h_vIn
  have : vIn ≠ v' := by subst vIn; exact offsetIn_neq
  show vIn.offsetOut v' = some v
  cases varKind
  case deBruijn =>
    rw [offsetOut, offsetOutDeBruijn]
    rw [toNat]
    rw [ite_cond_eq_false (h := eq_false this)]
    rw [←apply_ite]
    rw [Option.some_inj]
    if h : toNat v < v' then
      have : vIn = v := by grind only [= offsetIn_notation, offsetIn, offsetInDeBruijn]
      clear h_vIn
      subst vIn
      have : ¬ toNat v > v' := by grind only
      rw [if_neg this]
    else
      have h_vIn : vIn = toNat v + 1 := by grind only [= offsetIn_notation, offsetIn,
        offsetInDeBruijn]
      have : toNat vIn > v' := by grind only
      rw [if_pos this]
      rw [h_vIn]
      rfl
  case named =>
    sorry

@[grind =, simp]
theorem Var.offsetIn_offsetOut_of_isSome
    (h : (v↓v').isSome)
    : (v↓v').bind (·↓v') = some v := by
  sorry

@[grind =]
theorem Var.offsetIn_offsetOut_eq_ite
    : (v↓v').bind (·↓v') = if v = v' then none else some v := by
  sorry

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
    : (x↓y).get!↓z = (x↓(z↑y)).bind (·↓y) :=
  sorry

@[grind =, simp]
theorem Var.offsetOut_eq_none_iff : v↓v' = none ↔ v = v' := by
  grind =>
    instantiate only [usr offsetOut_isSome_of_neq]
    instantiate only [= offsetOut_isSome]
    cases #5373
    · instantiate only [= Option.isSome_none]
    · instantiate only [= offsetOut_eq_none]

theorem Var.offsetOut_bind_offsetOut : (x↓y).bind (·↓z) = (x↓(z↑y)).bind (·↓y) := by
  rw [Var.bind_offsetOut_eq_ite]
  split
  · subst y
    symm
    rw [Option.bind_eq_none_iff]
    intro x' h
    rw [offsetOut_eq_none_iff]
    sorry
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

