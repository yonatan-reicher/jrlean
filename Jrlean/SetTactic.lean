module

import Jrlean.Of
public meta import Lean
open Lean Elab Tactic Meta

/-!
A reimplementation of the `set` tactic from Mathlib. Original implementation in
https://github.com/leanprover-community/mathlib4/blob/c368140668f5fa16a1bd977448c1f665d48c3df4/Mathlib/Tactic/Set.lean#L29-L52.
-/

namespace Jrlean

public meta section

syntax (name := setTactic)
  "set " (binderIdent)? (" : " term)? " := " term (" with " " ← "? binderIdent)? : tactic

elab_rules : tactic
| `(tactic| set%$set $[$id]? $[: $ty]? := $val $[with $[←%$rev]? $h]?) =>
  withMainContext do
    -- Convert h from Option binderIdent to ident
    let id ← id.getDM `(binderIdent| this)
    let id ← match id with
      | `(binderIdent| $id:ident) => `(ident| $id)
      | _ => `(ident| a)
    -- Convert h from Option binderIdent to ident
    let h ← h.mapM fun h => match h with
      | `(binderIdent| $h:ident) => `(ident| $h)
      | _ => `(ident| h)
    -- If the type is given, elaborate using it. If not, infer the type of the value.
    let (ty, val) ← match ty with
      | some ty =>
        let ty ← Term.elabType ty
        pure (ty, ← elabTermEnsuringType val ty)
      | none =>
        let val ← elabTerm val none
        pure (← Meta.inferType val, val)
    let val ← Term.exprToSyntax val
    let ty ← Term.exprToSyntax ty
    evalTactic <| ← match h, rev with
      | some h, some none =>
        `(tactic| (generalize%$set $h : ($val : $ty) = $id at * ; symm at $h:ident))
      | some h, some (some _rev) => `(tactic| generalize%$set $h : ($val : $ty) = $id at *)
      | _, _ => `(tactic| generalize%$set ($val : $ty) = $id at *)
