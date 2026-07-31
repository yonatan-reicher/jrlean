module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}

def dec (v : Var') : Var' :=
  match varKind with
  | .deBruijn => v.toNat.pred
  | .named => ⟨v.name, v.depth.pred⟩

/-- I wanted to use `--` but that starts a comment... -/
postfix:75 (name:=varDec) "-" => dec

recommended_spelling "dec" for "-" in [dec, varDec]
