module

public import Jrlean.Coc.VarKind
import Jrlean.Coc.VarDecl

import Jrlean.InstanceInfer

namespace Jrlean.Coc

@[expose] public section

@[ext]
structure NamedVar where
  /-- The identifier given to the variable. -/
  name : Lean.Name
  /--
  De-Bruijn-style index give to the identifier. Basically, 'x' with depth 2 refers to a variable
  named 'x' that was defined before the 2 last local 'x' definitions.
  -/
  depth : Nat
  deriving DecidableEq, Inhabited, Hashable

instance : Repr NamedVar where
  reprPrec
    | ⟨name, 0⟩, _ => repr name
    | ⟨name, depth⟩, _ => "⟨" ++ repr name ++ ", " ++ repr depth ++ "⟩"

@[app_unexpander mk] public meta def NamedVar.unexpander : Lean.PrettyPrinter.Unexpander
  | `({ name := $n, depth := 0})
  | `(NamedVar.mk $n 0)
    => `($n)
  | `({ name := $n, depth := $d})
  | `(NamedVar.mk $n $d)
    => `(⟨$n, $d⟩)
  | _ => throw ()

/-- info: `x -/ #guard_msgs in #reduce show NamedVar from { name := `x , depth := 0 }
/-- info: ⟨`x, 12⟩ -/ #guard_msgs in #reduce show NamedVar from { name := `x , depth := 12 }

set_option linter.unusedVariables false in
/-- The type that represents this variable as a term. -/
@[grind]
def Var : {varKind : VarKind} → Type
  | .deBruijn => Nat
  | .named => NamedVar

variable {varKind : VarKind}

/-- Infer a definition by dispatching based on the underlying type. -/
local macro "infer " "instance " " : " typeClass:term : command => `(
  instance : $typeClass (@Var varKind) := by
    unfold Var
    cases varKind <;> (simp only ; infer_instance)
)
infer instance : Inhabited
infer instance : DecidableEq
infer instance : Hashable

abbrev Var' [varKind : VarKind] := @Var varKind

instance : Repr Var' :=
  match varKind with
  | .deBruijn => inferInstanceAs <| Repr Nat
  | .named =>
    { reprPrec v n :=
        if v.depth = 0 then Repr.reprPrec v.name n
        else Repr.reprPrec (show NamedVar from v) n }
