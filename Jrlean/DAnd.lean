module

public meta import Lean.PrettyPrinter.Delaborator
open Lean (bracketedExplicitBinders expandBracketedBinders)
open Lean.PrettyPrinter.Delaborator

namespace Jrlean

@[expose] public section

/-- A dependent conjuction. -/
@[grind, ext]
structure DAnd {p : Prop} (q : p → Prop) where
  fst : p
  snd : q fst

-- Notation taken directly from `Init.NotationExtra`.
macro:35 lhs:bracketedExplicitBinders " ∧' " rhs:term:35 : term =>
  .mk <$> expandBracketedBinders ``DAnd lhs rhs
-- This one is a generalization, allowing us to omit the name and brackets.
macro:35 lhs:term:36 " ∧' " rhs:term:35 : term =>
  `((_ : $lhs) ∧' $rhs)

namespace DAnd

@[app_unexpander DAnd] meta def unexpander : Lean.PrettyPrinter.Unexpander
  -- This is also taken from `Init.NotationExtra`.
  | `(DAnd fun ($x:ident : $lhs) => $rhs) => `(($x:ident : $lhs) ∧' $rhs)
  | _ => throw ()

-- These aren't
@[app_delab DAnd] meta def delaborator : Lean.PrettyPrinter.Delaborator.Delab := do
  let e ← SubExpr.getExpr
  match e.getAppArgs with
  | #[_lhs, rhsFunc] => do
    -- The right-hand side is a function from a proof of the left-hand side to a proof of the
    -- right-hand side.
    let lhsTerm ← SubExpr.withAppFn do SubExpr.withAppArg delab
    let rhsFuncTerm ← SubExpr.withAppArg do delab
    let boundName := getBoundName rhsFuncTerm
    let rhsTerm ← SubExpr.withAppArg do SubExpr.withBindingBody boundName do delab
    if ← isBoundNameUsed rhsFunc then
      ``(($(Lean.mkIdent boundName):ident : $lhsTerm) ∧' $rhsTerm)
    else
      ``($lhsTerm ∧' $rhsTerm)
  | _ => failure
where
  getBoundName
    | `(fun ($x:ident : $_) => $_) => x.getId
    | `(fun $x:ident => $_) => x.getId
    | _ => `_
  isBoundNameUsed
    -- This time we need the actual name, not just the name to use for the syntax.
    | .lam _ _ body .. =>
      return body.hasLooseBVar 0
    | _ => return true -- Assume that it is

recommended_spelling "dand" for "∧'" in [DAnd]

variable {p p₁ p₂ : Prop} {q : p → Prop}

@[grind ., simp]
theorem intro (left : p) (right : q left) : (h : p) ∧' q h := ⟨left, right⟩

theorem and_of_dand : p₁ ∧' p₂ → p₁ ∧ p₂ := by
  rintro ⟨hp, hq⟩
  exact ⟨hp, hq⟩

theorem dand_of_and : p₁ ∧ p₂ → p₁ ∧' p₂ := by
  rintro ⟨hp, hq⟩
  exact ⟨hp, hq⟩

macro "and" : tactic => `(tactic| apply DAnd.intro)

end DAnd
