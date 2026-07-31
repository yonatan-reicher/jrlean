module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}

/-- Prefer using `Var.Shadowed`. -/
def shadowedImpl (v : Var') : Prop :=
  match varKind with
  | .deBruijn => 0 < v.toNat
  | .named => 0 < v.depth

class Shadowed (v : Var') : Prop where
  shadowed : v.shadowedImpl

class Unshadowed (v : Var') : Prop where
  unshadowed : ¬ v.Shadowed
