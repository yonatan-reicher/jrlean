module

public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}

def shadows (x y : Var') : Prop :=
  match varKind with
  | .deBruijn => x.toNat < y.toNat
  | .named => x.name = y.name ∧ x.depth < y.depth

abbrev shadowsEq (x y : Var') := x.shadows y ∨ x = y

infix:50 (name:=term_shadows) " < " => shadows
infix:50 (name:=term_shadowsEq) " ≤ " => shadowsEq
infix:50 (name:=term_shadowsEq') " <= " => shadowsEq

recommended_spelling "shadows" for "<" in [shadows, term_shadows]
recommended_spelling "shadowsEq" for "≤" in [shadowsEq, term_shadowsEq, term_shadowsEq']

instance : DecidableRel (@shadows varKind) := by
  intro x y
  unfold shadows
  cases varKind <;> infer_instance
