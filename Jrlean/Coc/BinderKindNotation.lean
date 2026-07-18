module

import Lean
public meta import Jrlean.Coc.BinderKind

/-!
The reason for the module being here, and so small, is because I wanted the definitions in the
imported files to not be marked as `meta`. For that, you have to `meta import` them to use in a
macro.
-/

namespace Jrlean.Coc

syntax (name := term_binderKind) binderKind : term
macro_rules
  | `(λ) => ``(BinderKind.lam)
  | `(Π) => ``(BinderKind.pi)

@[app_unexpander BinderKind.lam, app_unexpander BinderKind.pi]
public meta def BinderKind.delab : Lean.PrettyPrinter.Unexpander
  | `(BinderKind.lam) => `(λ)
  | `(BinderKind.pi) => `(Π)
  | _ => throw ()
