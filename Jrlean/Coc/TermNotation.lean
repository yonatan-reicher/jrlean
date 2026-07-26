module

public import Jrlean.Coc.Term
public import Jrlean.Coc.VarConversions
public meta import Jrlean.Coc.BinderKindNotation
public meta import Jrlean.Coe

import Lean
import Jrlean.Of

open Lean (mkIdent quote)
open Lean.PrettyPrinter (Unexpander)

open Jrlean

namespace Jrlean.Coc

public section

variable {varKind : VarKind}

-- These allow us to write just `prop` and `type`.
@[match_pattern] public abbrev prop : Term' := Term.prop
@[match_pattern] public abbrev type : Term' := Term.type
-- These make the notation appear colored! ~^-^~
notation "prop" => prop
notation "type" => type
-- And these fix the unexpander generated.
@[app_unexpander Term.prop] meta def Term.prop.unexpander : Unexpander | _ => ``(prop)
@[app_unexpander Term.type] meta def Term.type.unexpander : Unexpander | _ => ``(type)

-- Write applications as `f a`.
-- Also allow us to treat things that convert to terms as applications.
instance : CoeFun Term' fun _ => Term' → Term' where coe t := t.app
-- instance : CoeFun Var' fun _ => Term' → Term' where coe t := (Term.var t).app
instance {α} [CoeHOTC α Term'] : CoeFun α fun _ => Term' → Term' where
  coe a := Term.app a
-- instance : CoeFun Lean.Name fun _ => @Term .named → @Term .named where
--   coe t := @Term.app .named (@Term.var .named t)
@[app_unexpander app] meta def Term.app.unexpander : Unexpander
  | `(Term.app $f $a) => ``($f $a)
  | _ => throw ()

#guard_expr (fun (f a : Term') => f a) = (fun (f a : Term') => f.app a)

-- λ x : ty. body
macro:arg k:binderKind ws x:term:max " : " ty:term:max " . " body:term:min : term => do
  ``(Term.binder $k:term $x $ty $body)
@[app_unexpander binder] meta def Term.binder.unexpander : Unexpander
  | `(Term.binder $k $x $ty $body) =>
    match k with
    | `(λ) => `(λ $x : $ty . $body)
    | `(Π) => `(Π $x : $ty . $body)
    | _ => throw ()
  | _ => throw ()

-- `x or 12
-- We can already write these as `Var` via coersions defined in `VarConversions.lean`. Just need to
-- define coersions to terms.
instance : CoeOut Var' Term' where coe := .var
instance : Coe    Var' Term' where coe := .var
public abbrev var : @Var varKind → @Term varKind := Term.var
@[app_unexpander var] meta def Term.var.unexpander : Unexpander
  | `(Term.var $v) => ``($v)
  | _ => throw ()

/-- info: `x -/ #guard_msgs in #reduce (`x : @Term .named)
/-- info: `x -/ #guard_msgs in #reduce @Term.var .named ⟨`x, 0⟩
/-- info: ⟨`x, 12⟩ -/ #guard_msgs in #reduce @Term.var .named ⟨`x, 12⟩
/-- info: Π `x : type . `f `x -/ #guard_msgs in #reduce Π `x : (@Term.type .named) . `f `x
/-- info: Π `x : type . `f `x -/ #guard_msgs in #reduce Π `x : type . `f `x
/-- info: λ `x : type . `f `x -/ #guard_msgs in #reduce λ `x : type . `f `x
