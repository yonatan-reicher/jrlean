module

public import Jrlean.Coc.VarOffseting

import Jrlean.SetTactic

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}
variable {v v' : Var'}

attribute [local grind .]
  Var.offsetIn
  Var.offsetOut
  Var.offsetInDeBruijn
  Var.offsetInNamed
  Var.offsetOutDeBruijn
  Var.offsetOutNamed
  NamedVar.ext

@[grind _=_]
private theorem simp : v↓v' = v.offsetOut v' := rfl

@[simp]
theorem Var.offsetOut_isSome_of_neq
    (h : v ≠ v')
    : (v↓v').isSome := by
  grind only [= eq_2, = simp, offsetOut, offsetOutDeBruijn, = Option.isSome_some, offsetOutNamed,
    NamedVar.ext, #aa1a, #616e, #75b3, #9840]
grind_pattern Var.offsetOut_isSome_of_neq => v↓v'

@[grind =, simp]
theorem Var.offsetOut_eq_none_of_eq : v↓v = none := by
  grind only [= simp, offsetOut, offsetOutDeBruijn, offsetOutNamed, #aa1a]

@[grind =, simp]
theorem Var.offsetOut_isSome
    : (v↓v').isSome = (v ≠ v') := by
  grind only [usr offsetOut_isSome_of_neq, = simp, offsetOut, offsetOutDeBruijn,
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
  simp
  grind only [offsetIn, offsetInDeBruijn, offsetInNamed, #aa1a, #0019, #46c1, #8585]

@[grind =, simp]
theorem Var.offsetIn_offsetOut : (v↑v')↓v' = some v := by
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
      have : vIn = v := sorry
      clear h_vIn
      subst vIn
      have : ¬ toNat v > v' := by grind only
      rw [if_neg this]
    else
      have h_vIn : vIn = toNat v + 1 := sorry
      have : toNat vIn > v' := by grind
      rw [if_pos this]
      rw [h_vIn]
      rfl
  case named =>
    sorry
