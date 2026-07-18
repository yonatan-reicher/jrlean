module

public import Jrlean.Coc.VarKind
import Jrlean.Coc.VarDecl

import Jrlean.InstanceInfer

namespace Jrlean.Coc

public section

/-- The type that represents this variable as a term. -/
abbrev Var : [VarKind] → Type
  | .deBruijn => Nat
  | .named => Lean.Name × Nat

variable {varKind : VarKind}

abbrev Var.name (v : @Var .named) : Lean.Name := v.1
abbrev Var.depth (v : @Var .named) : Nat := v.2

instance : Inhabited Var infer
instance : DecidableEq Var infer
instance : Hashable Var infer

instance : Repr Var :=
  match varKind with
  | .deBruijn => inferInstance
  | .named =>
    { reprPrec v n :=
        if v.depth = 0 then Repr.reprPrec v.name n
        else Repr.reprPrec v n }

variable {vkind : VarKind}

-- TODO: Move these into a file about substitution

/-- Updates a variable term to be of under a new binder. -/
@[grind, simp]
def Var.moveIntoBinder (var : Var) (bound : Var) : Var :=
  match vkind with
  | .deBruijn =>
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
  | .deBruijn =>
    if var = unbound then none
    else if var > unbound then some (var - 1)
    else some var
  | .named =>
    if var.name != unbound.name then some var
    else if var.depth = unbound.depth then none
    else if var.depth > unbound.depth then some (var.name, var.depth - 1)
    else some var
