module

public import Jrlean.Coc.Term
public meta import Jrlean.Coc.BinderKindNotation

open Lean (mkIdent quote)
open Lean.PrettyPrinter (Unexpander)

namespace Jrlean.Coc

public section

variable {varKind : VarKind}

-- These allow us to write just `prop` and `type`, and they also infer the variable kind from the
-- types instead of from the context.
public abbrev prop : Term := Term.prop
public abbrev type : Term := Term.type
-- These make the notation appear colored! ~^-^~
notation "prop" => prop
notation "type" => type
-- And these fix the unexpander generated.
@[app_unexpander Term.prop] meta def Term.prop.unexpander : Unexpander | _ => ``(prop)
@[app_unexpander Term.type] meta def Term.type.unexpander : Unexpander | _ => ``(type)

-- Write applications as `f a`
instance : CoeFun Term (fun _ => Term → Term) where
  coe t := t.app
@[app_unexpander app] meta def Term.app.unexpander : Unexpander
  | `(Term.app $f $a) => ``($f $a)
  | _ => throw ()

-- λ x : ty. body
macro:arg k:binderKind ws x:ident " : " ty:term:max " . " body:term:min : term => do
  ``(@Term.binder VarKind.named $k:term $(quote x.getId) $ty $body)
@[app_unexpander binder] meta def Term.binder.unexpander : Unexpander
  | `(Term.binder $k $x:name $ty $body) =>
    match k with
    | `(λ) => `(λ $(mkIdent x.getName) : $ty . $body)
    | `(Π) => `(Π $(mkIdent x.getName) : $ty . $body)
    | _ => throw ()
  | _ => throw ()

-- var x or var `x or var 12
public abbrev var := Term.var
notation:arg "var " x:max => var x
macro "var " x:ident : term => `(@Term.var .named ($(quote x.getId), 0))
macro "var " n:num : term => `(@Term.var .deBruijn $n)
@[app_unexpander Term.var] meta def Term.var.unexpander : Unexpander
  | `(Term.var ($a:name, 0)) => `(var $(mkIdent a.getName):ident)
  | `(Term.var $n:num) => `(var $n:num)
  | `(Term.var $a) => `(var $a:term)
  | _ => throw ()


/-- info: var x -/ #guard_msgs in #reduce var x
/-- info: var x -/ #guard_msgs in #reduce @Term.var .named (`x, 0)
/-- info: var (`x, 12) -/ #guard_msgs in #reduce @Term.var .named (`x, 12)
/-- info: Π x : type . (var f) var x -/ #guard_msgs in
#reduce Π x : (@Term.type .named) . (var f) var (`x, 0)
