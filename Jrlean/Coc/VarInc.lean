module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}

def inc (v : Var') : Var' :=
  match varKind with
  | .deBruijn => v.toNat.succ
  | .named => ⟨v.name, v.depth.succ⟩

postfix:75 (name:=varInc) "++" => inc

recommended_spelling "inc" for "++" in [inc, varInc]
