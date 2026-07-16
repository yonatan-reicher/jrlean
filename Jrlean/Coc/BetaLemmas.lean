module

import Jrlean.SetTactic
import Jrlean.ByContra
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Coc.Beta
public import Jrlean.Coc.BetaHeadInduction

namespace Jrlean.Coc

variable [varKind : VarKind]

@[simp]
theorem app_lam_equiv {v ty body a}
: .app (.lam v ty body) a =β body.moveOutOfBinder v.toVar a := .beta

grind_pattern app_lam_equiv => Term.app (.lam v ty body) a

theorem app_equiv_reduce {f a v ty body}
: f =β .lam v ty body -> .app f a =β body.moveOutOfBinder v.toVar a := by
  intro h_f
  calc
    .app f a =β .app (.lam v ty body) a := .app_congr h_f .refl
    _ =β body.moveOutOfBinder v.toVar a := app_lam_equiv

grind_pattern app_equiv_reduce => f =β .lam v ty body, f.app a
grind_pattern app_equiv_reduce => f.app a =β body.moveOutOfBinder v.toVar a, Term.lam v ty body

@[grind., grind→]
theorem app_congr {f₁ f₂ a₁ a₂}
: f₁ =β f₂ → a₁ =β a₂ → f₁.app a₁ =β f₂.app a₂ :=
  fun h_f h_a => .app_congr h_f h_a

@[grind., grind! =>]
theorem binder_congr {k v ty₁ ty₂ body₁ body₂}
: ty₁ =β ty₂ → body₁ =β body₂ → .binder k v ty₁ body₁ =β .binder k v ty₂ body₂ :=
  fun h_ty h_body => .binder_congr h_ty h_body

@[grind ., simp]
theorem prop_nequiv_type : .prop ≠β .type := by
  -- We need a symmetric induction hypothesis
  suffices ∀ t₁ t₂, t₁ =β t₂ → ¬(t₁ = .prop ∧ t₂ = .type) ∧ ¬(t₁ = .type ∧ t₂ = .prop) by grind
  intro t₁ t₂
  intro h
  induction h
  case beta v ty body arg =>
    apply And.intro <;> (rintro ⟨h₁, h₂⟩; contradiction)
  case refl t => grind only
  case symm t₁ t₂ h ih => grind only
  case trans t₁ t₂ t₃ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨ih₁₁, ih₁₂⟩ := ih₁
    obtain ⟨ih₂₁, ih₂₂⟩ := ih₂
    apply And.intro
    · rintro ⟨_, _⟩
      subst t₁ t₃
      simp_all only [true_and, reduceCtorEq, false_and, not_false_eq_true, and_true, and_self]

#print Term.BetaEquiv.recOn

theorem moveOutOfBinder_equiv_prop {body v arg}
: body.moveOutOfBinder v arg =β .prop → body =β .prop := by
  intro h_moveOut_equiv_prop
  induction body generalizing v arg
  case prop => rfl
  case type => rfl

theorem app_equiv_prop_unique {f a}
: .app f a =β .prop → ∀ t, .app f a =β t → t = .prop ∨ (∃ f' a', t = .app f' a') := by
  let isApp (t : Term) := ∃ f a, t = .app f a
  -- Change the goal to be easier for induction
  suffices ∀ t, isApp t → t =β .prop → ∀ t', t =β t' → t' = .prop ∨ isApp t' by
    apply this
    show isApp (.app f a)
    exists f, a
  clear f a
  intro t
  induction t using Term.betaHeadInduction
  iterate 4 nofun -- All cases but application are trivial
  case betaHead v ty body arg ih_ty ih_body =>
    intro h_isApp; clear h_isApp
    intro h_app_equiv_prop
    intro t' h_app_equiv_t'
    show t' = .prop ∨ isApp t'
    have : body.moveOutOfBinder v.toVar arg =β t' := by
      apply Term.BetaEquiv.trans
      · symm; apply Term.BetaEquiv.beta (ty:=ty)
      · exact h_app_equiv_t'
    have : body.moveOutOfBinder v.toVar arg =β .prop := by
      apply Term.BetaEquiv.trans
      · symm; apply Term.BetaEquiv.beta (ty:=ty)
      · exact h_app_equiv_prop
    by_cases t' = .prop
    next => left; assumption
    next =>

    apply ih_body
    · done
    · done
    · done
    ∎
  case app f a h_betaHead_eq_none ih_f ih_a =>
    intro h_isApp_app; clear h_isApp_app
    intro h_app_equiv_prop
    intro t' h_app_equiv_t'
    show t' = .prop ∨ isApp t'
    cases f
    case type =>
      induction h_app_equiv_prop


  case prop => nofun

@[grind]
theorem binder_nequiv_prop_type_var {k v ty body t}
: .binder k v ty body =β t → t ≠ .prop ∧ t ≠ .type ∧ ∀ v, t ≠ .var v := sorry

/-

theorem binder_equiv_binder {k₁ k₂ v₁ v₂ ty₁ body₁ ty₂ body₂}
: .binder k₁ v₁ ty₁ body₁ =β .binder k₂ v₂ ty₂ body₂
→ k₁ = k₂ ∧ v₁ = v₂ ∧ ty₁ =β ty₂ ∧ body₁ =β body₂ := by
  apply Term.BetaEquiv.rec (motive := fun
    | .binder k₁ v₁ ty₁ body₁, .binder k₂ v₂ ty₂ body₂ =>
       k₁ = k₂ ∧ v₁ = v₂ ∧ ty₁ =β ty₂ ∧ body₁ =β body₂
    | _, _ => True)
  -- induction h using Term.BetaEquiv.rec
  case beta => simp only [implies_true]
  case refl =>
    intro t
    cases t <;> trivial
  case symm =>
    intro t₁ t₂ h ih
    cases t₁ <;> cases t₂
    case binder.binder => grind
    all_goals trivial
  case trans =>
    intro t₁ t₂ t₃ h₁ h₂ ih₁ ih₂
    cases t₁ <;> cases t₂ <;> cases t₃
    case binder.binder.binder => grind
    all_goals try trivial
  match h with
  | .refl => trivial
  | .symm h => exact (binder_equiv_binder h).symm
  | .binder h_ty h_body =>
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · exact h_ty
    · exact h_body

theorem binder_equiv_binder_or_app {k v ty₁ body₁ t}
: .binder k v ty₁ body₁ =β t
→ (∃ ty₂ body₂, t = .binder k v ty₂ body₂) ∨ (∃ f a, t = .app f a) := by
  intro h
  match t with
  | .binder k' v' ty₂ body₂ =>
    left
    exists ty₂, body₂
    rfl

-/
