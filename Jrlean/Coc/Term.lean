module

public import Jrlean.Coc.VarKind
public import Jrlean.Coc.VarDecl
public import Jrlean.Coc.Var
public import Jrlean.Coc.BinderKind
import Jrlean.Coc.VarConversions
import Jrlean.Coc.BinderKindNotation

namespace Jrlean.Coc

public section

/-- A term in the Calculus of Constructions. -/
@[grind]
inductive Term {varKind : VarKind} : Type where
  /-- The type of propositions. -/
  | prop : Term
  /-- The type of types, except itself. -/
  | type : Term
  /-- A variable. -/
  | var (v : Var') : Term
  /-- An application of a function to an argument. -/
  | app (f : @Term varKind) (a : @Term varKind) : Term
  /-- Declares a binder from some variable of some type to a body. -/
  | binder (k : BinderKind) (x : VarDecl') (ty : @Term varKind) (body : @Term varKind) : Term
  deriving DecidableEq, Inhabited, Hashable

/-- A version of `Term` that infers the variable kind via type-class inference. -/
abbrev Term' [varKind : VarKind] := @Term varKind

variable {varKind : VarKind}

@[match_pattern] abbrev Term.lam := @Term.binder varKind (λ)
@[match_pattern] abbrev Term.pi  := @Term.binder varKind (Π)
