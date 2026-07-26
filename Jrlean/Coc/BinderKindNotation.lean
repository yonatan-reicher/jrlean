module

import Lean
public import Jrlean.Coc.BinderKind
import Jrlean.Of

open Lean (TSyntax)
open Lean.PrettyPrinter (Unexpander)

namespace Jrlean.Coc

public section

/-- Either λ or Π -/
syntax binderKind := "λ" <|> "Π"

syntax (name := term_binderKind) binderKind : term
macro_rules
  | `(λ) => ``(BinderKind.lam)
  | `(Π) => ``(BinderKind.pi)

def BinderKind.symbol : BinderKind → String
  | BinderKind.lam => "λ"
  | BinderKind.pi => "Π"

def BinderKind.toSyntax (b : BinderKind) : TSyntax ``binderKind :=
  Lean.mkAtom b.symbol
  |>.node1 .none of `token ++ .mkSimple b.symbol
  |>.node1 .none ``binderKind
  |> .mk

def _root_.Lean.TSyntax.toTerm (stx : TSyntax ``binderKind) : Lean.Term :=
  stx.raw.node1 .none ``term_binderKind |> .mk

instance : CoeOut (TSyntax ``binderKind) Lean.Term where
  coe stx := stx.toTerm

def BinderKind.ofSyntax : TSyntax ``binderKind → BinderKind
  | `(binderKind|λ) => BinderKind.lam
  | `(binderKind|Π) => BinderKind.pi
  | _ => panic! "Invalid binder kind syntax"

-- Convertable to syntax
instance : Lean.Quote BinderKind ``binderKind where quote b := b.toSyntax
instance : Lean.Quote BinderKind `term where quote b := b.toSyntax

@[app_unexpander lam, app_unexpander pi]
public meta def BinderKind.unexpander : Unexpander
  | `(BinderKind.lam) => `(λ)
  | `(BinderKind.pi) => `(Π)
  | _ => throw ()

/-- info: λ -/ #guard_msgs in #reduce BinderKind.lam
/-- info: Π -/ #guard_msgs in #reduce BinderKind.pi
/-- info: λ : BinderKind -/ #guard_msgs in #check λ
/-- info: Π : BinderKind -/ #guard_msgs in #check Π
