module

import Jrlean.Coc.Basic

-- TODO: Check if notation can be scoped, and if so, try to define scoped notation that doesn't need
-- to be a dsl

namespace Jrlean.Coc

/--
Syntax of variables in terms CoC terms. Can be either an identifier, or a Lean
term enclosed in parentheses. When just an identifier, it is interpreted as a
`Lean.Name`.
-/
declare_syntax_cat cocVar

-- Declare the members of the syntax category.
syntax ident : cocVar
syntax "_" : cocVar
syntax "{" term "}" : cocVar

-- Declare how the syntax category is used.
syntax "cocVarToTerm " cocVar : term

macro_rules
  | `(cocVarToTerm $x:ident) => return (Lean.quote x.getId : Lean.Term)
  | `(cocVarToTerm _) => return (Lean.quote Lean.Name.anonymous : Lean.Term)
  | `(cocVarToTerm {$x:term}) => return x

/--
Syntax of terms in the Calculus of Constructions.
Can be converted to a `Term` using the `cocTermToTerm` macro.
-/
declare_syntax_cat cocTerm
-- Declare the members of the syntax category.
-- Precedence table:
-- 0: application
-- 1: lambda, pi
-- 2: atoms
syntax:2 "Type" : cocTerm
syntax:2 "Prop" : cocTerm
syntax:2 cocVar : cocTerm
syntax:0 cocTerm:0 cocTerm:1 : cocTerm
syntax:1 "λ" cocVar ":" cocTerm:0 "." cocTerm:0 : cocTerm
syntax:1 "Π" cocVar ":" cocTerm:0 "." cocTerm:0 : cocTerm
syntax:2 "{" term:0 "}" : cocTerm
syntax:2 "(" cocTerm:0 ")" : cocTerm
-- How the syntax category is used.
syntax "cocTermToTerm " cocTerm:0 : term
macro_rules
  | `(cocTermToTerm Type) => ``(Term.type)
  | `(cocTermToTerm Prop) => ``(Term.prop)
  | `(cocTermToTerm $v:cocVar) => ``(Term.var (varKind:=VarKind.named) (cocVarToTerm $v, 0))
  | `(cocTermToTerm $f:cocTerm $a:cocTerm) => ``(Term.app (cocTermToTerm $f) (cocTermToTerm $a))
  | `(cocTermToTerm λ $x:cocVar : $ty:cocTerm . $body:cocTerm) =>
    ``(Term.binder (varKind:=VarKind.named) BinderKind.lam (cocVarToTerm $x) (cocTermToTerm $ty) (cocTermToTerm $body))
  | `(cocTermToTerm Π $x:cocVar : $ty:cocTerm . $body:cocTerm) =>
    ``(Term.binder (varKind:=VarKind.named) BinderKind.pi (cocVarToTerm $x) (cocTermToTerm $ty) (cocTermToTerm $body))
  | `(cocTermToTerm {$x:term}) => return x
  | `(cocTermToTerm ($x:cocTerm)) => `(cocTermToTerm $x)

