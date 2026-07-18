module

public import Jrlean.Coc.Var

namespace Jrlean.Coc

public section

inductive BinderKind
  | lam
  | pi
  deriving Inhabited, DecidableEq, Hashable, Repr

notation "λ" => BinderKind.lam
notation "Π" => BinderKind.pi

instance BinderKind.instRepr : Repr BinderKind where
  reprPrec
    | lam, _ => "λ"
    | pi, _ => "Π"

/-- A term in the Calculous of Constructions. -/
inductive Term [varKind : VarKind]
  /-- The type of types -/
  | type
  /-- The type of propositions -/
  | prop
  /-- A variable -/
  | var (v : Var)
  /-- An application of a function to an argument -/
  | app (f : Term) (a : Term)
  /-- Declares a binder from x of type ty to body -/
  | binder (k : BinderKind) (x : VarDecl) (ty : Term) (body : Term)
  deriving Inhabited, DecidableEq, Hashable

@[match_pattern] abbrev Term.lam [VarKind] := Term.binder .lam
@[match_pattern] abbrev Term.pi [VarKind] := Term.binder .pi

