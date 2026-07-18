module

import Lean.Meta

namespace Jrlean.Coc

@[expose] public section

inductive BinderKind where
  /-- λ -/
  | lam
  /-- Π -/
  | pi
  deriving DecidableEq, Inhabited, Hashable, Repr

/-- Either λ or Π -/
syntax binderKind := "λ" <|> "Π"

def BinderKind.symbol : BinderKind → String
  | BinderKind.lam => "λ"
  | BinderKind.pi => "Π"

def BinderKind.toSyntax (b : BinderKind) : Lean.TSyntax ``binderKind :=
  .mk <| Lean.mkAtom b.symbol

def BinderKind.toSyntaxTerm (b : BinderKind) : Lean.Term := .mk <| b.toSyntax.raw

def BinderKind.ofSyntax : Lean.TSyntax ``binderKind → BinderKind
  | `(binderKind|λ) => BinderKind.lam
  | `(binderKind|Π) => BinderKind.pi
  | _ => panic! "Invalid binder kind syntax"

-- Convertable to syntax
instance : Lean.Quote BinderKind ``binderKind where quote b := b.toSyntax
instance : Lean.Quote BinderKind `term where quote b := b.toSyntaxTerm
