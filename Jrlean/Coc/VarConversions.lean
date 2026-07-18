module

public import Jrlean.Coc.VarKind
public import Jrlean.Coc.VarDecl
public import Jrlean.Coc.Var

namespace Jrlean.Coc

@[expose] public section

variable {varKind : VarKind}

@[grind, simp]
def VarDecl.toVar (decl : VarDecl) : Var :=
  match varKind with
  | .deBruijn => 0
  | .named => (decl, 0)
abbrev Var.ofDecl (decl : VarDecl) := decl.toVar

@[grind, simp]
def Var.toDecl (v : Var) : VarDecl :=
  match varKind with
  | .deBruijn => ()
  | .named => v.1
abbrev VarDecl.ofVar (v : Var) := v.toDecl

instance : CoeTail VarDecl Var where coe := .ofDecl
instance : CoeTail Var VarDecl where coe := .ofVar
