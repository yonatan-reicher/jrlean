module

public import Jrlean.Coc.TermFreeVars
public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermNotation

import Jrlean.Coc.VarOffsetingLemmas
import Jrlean.Coc.TermOffsetingLemmas

namespace Jrlean.Coc.Term

public section

variable {varKind : VarKind}
variable {t t' a b c d : Term'}
variable {x y z : Var'}

attribute [local grind .]
  Term.freeVars

theorem freeVars_offsetOut
    (h : (t↓x).isSome)
    : (t↓x).get!.freeVars = t.freeVars.filterMap (·↓x) := by
  induction t generalizing x
  iterate 2 next => grind =>
    instantiate only [= offsetOut_sort, freeVars]
    instantiate only [= Option.get!_some, = List.filterMap_nil]
  case var =>
    grind =>
      instantiate only [= offsetOut.notation, = offsetOut_var, freeVars]
      instantiate only [usr Var.offsetOut_eq_some_of_neq, = offsetOut.eq_3, = Option.isSome_map,
        = List.filterMap_cons]
      instantiate only [= Var.offsetOut_isSome, = Option.bind_apply]
      cases #4431 <;>
        instantiate only [= Option.bind_some] <;>
          instantiate only [= List.filterMap_nil, = Option.get!_some] <;>
            instantiate only [freeVars]
  case app f a ih_f ih_a =>
    have : ((f a)↓x).get! = (f↓x).get! (a↓x).get! := by
      grind only [= offsetOut_app_of_isSome, = Option.get!_some]
    rw [this]; clear this
    unfold freeVars
    repeat rw [List.filterMap_append]
    rw [ih_f (by grind only [= offsetOut_app_isSome])]
    rw [ih_a (by grind only [= offsetOut_app_isSome])]
    done
  case binder k y ty body ih_ty ih_body =>
    rw [offsetOut_binder_of_isSome, Option.get!_some]
    unfold freeVars
    show (ty↓x).get!.freeVars ++ (body↓(x↑↑y)).get!.freeVars.filterMap (fun v' => v'↓↑y) =
      (ty.freeVars ++ body.freeVars.filterMap (fun v' => v'↓↑y)).filterMap (fun x_1 => x_1↓x)
    rw [ih_ty, ih_body]
    rw [List.filterMap_append]
    congr 1
    repeat rw [List.filterMap_filterMap]
    congr
    funext z
    conv => rhs; rw [Var.offsetOut_bind_offsetOut]
    exact?
    rw [Var.offsetIn_offsetOut_eq_ite]
    grind
    simp only [List.filterMap_append, List.append_cancel_left_eq]
    rfl
    rw [ih_ty, ih_body]
    simp
    sorry

theorem freeVars_offsetIn
    : (t↑x).freeVars = t.freeVars.map (·↑x) := by
  induction t generalizing x -- In the binder case, we use `x↑y` instead of `x`
  iterate 2 next =>
    grind only [= Term.offsetIn_sort, Term.freeVars, = List.map_nil]
  case var =>
    grind =>
      instantiate only [= Term.offsetIn_var, Term.freeVars]
      instantiate only [Term.freeVars, = List.map_cons]
      instantiate only [= List.map_nil]
  case app f a ih_f ih_a =>
    grind =>
      instantiate only [= offsetIn_app, freeVars]
      instantiate only [#40ad, #dc2f, freeVars, = List.map_append]
  case binder k y ty body ih_ty ih_body =>
    simp
    unfold freeVars
    rw [ih_ty, ih_body]
    rw [List.map_append]
    suffices (body.freeVars.map (·↑(x↑y)) |>.filterMap (·↓y))
           = (body.freeVars.filterMap (·↓y) |>.map (·↑x)) by congr
    rw [List.filterMap_map, List.map_filterMap]
    congr
    funext z
    suffices (z↑(x↑↑y))↓↑y = (z↓↑y).map (·↑x) by simpa only [Function.comp_apply]
    if h_y : z = y then
      subst z
      rw [Var.offsetOut_eq_none, Option.map_none]
      grind
    else
      obtain ⟨z', h_z'⟩ := Var.offsetOut_eq_some_of_neq h_y
      rw [h_z', Option.map_some]
      

