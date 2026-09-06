module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions
public import Jrlean.Coc.Offseting
public import Jrlean.Coc.Shadows
public import Jrlean.Coc.VarInc
public import Jrlean.Coc.VarDec

import Jrlean.Of

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}

@[grind]
def Var.offsetIn (v bound : @Var varKind) : Var' :=
  if bound ≤ v then v++ else v

@[grind]
def Var.offsetOut (v unbound : @Var varKind) : Option Var' :=
  if unbound = v then none
  else some of if unbound < v then v- else v

instance : Offset varKind Var' where
  offsetIn v bound := v.offsetIn bound
  offsetOut v unbound := v.offsetOut unbound
