module

import Jrlean.InstanceInfer

namespace Jrlean.Coc

public section

/-- Either debruijn indices or named identifiers. -/
class inductive VarKind where
  | debruijn
  | named
  deriving Inhabited, DecidableEq, Hashable, Repr

/-- The type of data that's needed to declare a variable of a given kind. -/
abbrev VarDecl : [VarKind] → Type
  | .debruijn => Unit
  | .named => Lean.Name

instance : Inhabited Lean.Name where
  default := `_

instance [VarKind] : Inhabited VarDecl infer
instance [VarKind] : DecidableEq VarDecl infer
instance [VarKind] : Repr VarDecl infer
instance [VarKind] : Hashable VarDecl infer

/-- The type that represents this variable as a term. -/
abbrev Var : [VarKind] → Type
  | .debruijn => Nat
  | .named => Lean.Name × Nat

abbrev Var.name (v : @Var .named) : Lean.Name := v.1
abbrev Var.depth (v : @Var .named) : Nat := v.2

instance [VarKind] : Inhabited Var infer
instance [VarKind] : DecidableEq Var infer
instance [VarKind] : Hashable Var infer

instance [varKind : VarKind] : Repr Var :=
  match varKind with
  | .debruijn => inferInstance
  | .named =>
    { reprPrec v n := if v.2 = 0 then Repr.reprPrec v.1 n else Repr.reprPrec v n }

variable {vkind : VarKind}

/-- Updates a variable term to be of under a new binder. -/
@[grind, simp]
def Var.moveIntoBinder (var : Var) (bound : Var) : Var :=
  match vkind with
  | .debruijn =>
    if var < bound then var
    else var + 1
  | .named =>
    if var.name != bound.name then var
    else if var.depth < bound.depth then var
    else (var.name, var.depth + 1)

/-- Updates a variable term to be of out of a given binder. -/
@[grind, simp]
def Var.moveOutOfBinder (var : Var) (unbound : Var) : Option Var :=
  match vkind with
  | .debruijn =>
    if var = unbound then none
    else if var > unbound then some (var - 1)
    else some var
  | .named =>
    if var.name != unbound.name then some var
    else if var.depth = unbound.depth then none
    else if var.depth > unbound.depth then some (var.name, var.depth - 1)
    else some var

/-- This returns a name to be used only for anonymous variables. Note that the
  variable can be accessed, they just shouldn't be. -/
abbrev VarDecl.anonymous : VarDecl :=
  match vkind with
  | .debruijn => ()
  -- | .named => Lean.Name.anonymous
  | .named => `_

@[grind, simp]
def VarDecl.toVar (decl : VarDecl) : Var :=
  match vkind with
  | .debruijn => 0
  | .named => (decl, 0)

@[grind, simp]
def Var.toDecl (v : Var) : VarDecl :=
  match vkind with
  | .debruijn => ()
  | .named => v.1
