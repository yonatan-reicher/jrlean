module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions
public import Jrlean.Coc.Offseting

import Jrlean.Of

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}

abbrev DVar := @Var .deBruijn
abbrev NVar := @Var .named

-- Offset In

@[grind]
def Var.offsetInDeBruijn (v bound : DVar) : DVar :=
  if v.toNat < bound.toNat then v
  else v.toNat + 1

@[grind]
def Var.offsetInNamed (v bound : NVar) : NVar :=
  if v.name != bound.name then v
  else if v.depth < bound.depth then v
  else ⟨v.name, v.depth + 1⟩

@[grind]
def Var.offsetIn (v bound : @Var varKind) : Var' :=
  match varKind with
  | .deBruijn => v.offsetInDeBruijn bound
  | .named => v.offsetInNamed bound

-- Offset Out

@[grind]
def Var.offsetOutDeBruijn (v : DVar) (unbound : DVar) : Option DVar :=
  if v = unbound then none
  else if v.toNat > unbound then some of v.toNat - 1
  else some v

@[grind]
def Var.offsetOutNamed (v : NVar) (unbound : NVar) : Option NVar :=
  if v.name != unbound.name then v
  else if v.depth = unbound.depth then none
  else if v.depth > unbound.depth then some ⟨v.name, v.depth - 1⟩
  else v

@[grind]
def Var.offsetOut (v unbound : @Var varKind) : Option Var' :=
  match varKind with
  | .deBruijn => v.offsetOutDeBruijn unbound
  | .named => v.offsetOutNamed unbound

instance : Offset varKind Var' where
  offsetIn v bound := v.offsetIn bound
  offsetOut v unbound := v.offsetOut unbound
