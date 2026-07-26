module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions
public import Jrlean.Coc.Term
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.VarOffseting
import Jrlean.Of

namespace Jrlean.Coc

@[expose]
public def Var.subst {varKind : VarKind} (x y : Var') (r : Term') : Term' :=
  (x ↓ y) |>.map var |>.getD r
