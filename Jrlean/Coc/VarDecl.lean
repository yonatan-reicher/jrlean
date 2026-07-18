module

public import Jrlean.Coc.VarKind

import Jrlean.InstanceInfer

namespace Jrlean.Coc

public section

/-- The type of data that's needed to declare a variable of a given kind. -/
abbrev VarDecl : [VarKind] → Type
  | .deBruijn => Unit
  | .named => Lean.Name

variable {varKind : VarKind}

instance : Inhabited Lean.Name where default := `_
instance : Inhabited VarDecl infer
instance : DecidableEq VarDecl infer
instance : Repr VarDecl infer
instance : Hashable VarDecl infer

/--
This returns a name to be used only for anonymous variables. Note that the variable can be accessed,
they just shouldn't be.
-/
abbrev VarDecl.anonymous : VarDecl :=
  match varKind with
  | .deBruijn => ()
  | .named => `_

