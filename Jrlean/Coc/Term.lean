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
inductive Term [VarKind] : Type where
  /-- The type of propositions. -/
  | prop : Term
  /-- The type of types, except itself. -/
  | type : Term
  /-- A variable. -/
  | var (v : Var) : Term
  /-- An application of a function to an argument. -/
  | app (f : Term) (a : Term) : Term
  /-- Declares a binder from some variable of some type to a body. -/
  | binder (k : BinderKind) (x : VarDecl) (ty : Term) (body : Term) : Term
  deriving DecidableEq, Inhabited, Hashable

@[match_pattern] abbrev Term.lam [VarKind] := Term.binder (λ)
@[match_pattern] abbrev Term.pi [VarKind]  := Term.binder (Π)
