module

public import Jrlean.Coc.VarKind
public import Jrlean.Coc.VarDecl
public import Jrlean.Coc.Var

namespace Jrlean.Coc

@[expose] public section

variable {varKind : VarKind}

instance {n} : OfNat (@Var .deBruijn) n where ofNat := n

@[grind, simp]
def VarDecl.toVar (decl : VarDecl') : Var' :=
  match varKind with
  | .deBruijn => 0
  | .named => ⟨decl, 0⟩
abbrev Var.ofDecl (decl : VarDecl') := decl.toVar

@[grind, simp]
def Var.toDecl (v : Var') : VarDecl' :=
  match varKind with
  | .deBruijn => ()
  | .named => v.1
abbrev VarDecl.ofVar (v : Var') := v.toDecl

@[simp]
abbrev Var.toNat (v : @Var .deBruijn) : Nat := v

@[simp]
abbrev Var.toNamedVar (v : @Var .named) : NamedVar := v

namespace VarDecl

@[coe, grind, simp]
def ofName (n : Lean.Name) : @VarDecl .named := n
instance : CoeOut Lean.Name (@VarDecl .named) := ⟨id⟩
instance : Coe    Lean.Name (@VarDecl .named) := ⟨id⟩

end VarDecl

namespace Var

-- Coe from Name,
@[coe, grind, simp]
def ofName (n : Lean.Name) : @Var .named := ⟨n, 0⟩
instance : CoeOut  Lean.Name (@Var .named) := ⟨ofName⟩
instance : Coe     Lean.Name (@Var .named) := ⟨ofName⟩
instance : CoeHead Lean.Name (@Var .named) := ⟨ofName⟩
instance : CoeTail Lean.Name (@Var .named) := ⟨ofName⟩

-- from Decl,
instance : CoeOut VarDecl' Var' := ⟨ofDecl⟩
instance : Coe    VarDecl' Var' := ⟨ofDecl⟩
attribute [coe] ofDecl VarDecl.toVar

end Var
-- instance : CoeOut Lean.Name NamedVar where coe n := ⟨n, 0⟩
-- instance : Coe    Lean.Name NamedVar where coe n := ⟨n, 0⟩
-- instance : CoeOut NamedVar (@Var .named)    where coe := id
-- instance : Coe    NamedVar (@Var .named)    where coe := id
-- instance : CoeOut Nat      (@Var .deBruijn) where coe := id
-- instance : Coe    Nat      (@Var .deBruijn) where coe := id
-- instance : CoeHead VarDecl' Var' where coe := .ofDecl
-- instance : CoeTail VarDecl' Var' where coe := .ofDecl
-- instance : CoeHead Var' VarDecl' where coe := .ofVar
-- instance : CoeTail Var' VarDecl' where coe := .ofVar
