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

-- Notation
@[simp] theorem Var.offsetIn.simp_notation (v bound : Var') : v↑bound = v.offsetIn bound := rfl
@[simp] theorem Var.offsetOut.simp_notation (v bound : Var') : v↓bound = v.offsetOut bound := rfl

-- Var kinds
@[simp] theorem Var.offsetIn.simp_deBruijn (v bound : @Var .deBruijn)
    : v.offsetIn bound = v.offsetInDeBruijn bound := rfl
@[simp] theorem Var.offsetOut.simp_deBruijn (v bound : @Var .deBruijn)
    : v.offsetOut bound = v.offsetOutDeBruijn bound := rfl

@[simp] theorem Var.offsetIn.simp_named (v bound : @Var .named)
    : v.offsetIn bound = v.offsetInNamed bound := rfl
@[simp] theorem Var.offsetOut.simp_named (v bound : @Var .named)
    : v.offsetOut bound = v.offsetOutNamed bound := rfl
