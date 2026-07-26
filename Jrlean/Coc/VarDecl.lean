module

public import Jrlean.Coc.VarKind

namespace Jrlean.Coc

@[expose] public section

set_option linter.unusedVariables false in
/-- The type of data that's needed to declare a variable of a given kind. -/
@[grind]
def VarDecl : {varKind : VarKind} → Type
  | .deBruijn => Unit
  | .named => Lean.Name

variable {varKind : VarKind}

instance : Inhabited Lean.Name where default := `_
local macro "infer " "instance " ": " typeClass:term : command => `(
  instance : $typeClass (@VarDecl varKind) := by
    unfold VarDecl
    cases varKind <;> (
      simp only
      infer_instance
    )
)
infer instance : Inhabited
infer instance : DecidableEq
infer instance : Repr
infer instance : Hashable

/-- A version of `VarDecl` that infers the variable kind via type-class inference. -/
abbrev VarDecl' [VarKind] := @VarDecl inferInstance

/--
This returns a name to be used only for anonymous variables. Note that the variable can be accessed,
they just shouldn't be.
-/
abbrev VarDecl.anonymous : VarDecl' :=
  match varKind with
  | .deBruijn => ()
  | .named => `_
