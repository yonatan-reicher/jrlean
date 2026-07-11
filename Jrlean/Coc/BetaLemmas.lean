module

import Jrlean.SetTactic
import Jrlean.ByContra
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Coc.Beta

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
/-- Describes the possible cases of beta equivalences -/
private inductive BetaEquivCases : Relation Term where
  | refl {t} : BetaEquivCases t t
  | binder_congr {k v ty₁ ty₂ body₁ body₂} : ty₁ =β ty₂ → body₁ =β body₂
    → BetaEquivCases (.binder k v ty₁ body₁) (.binder k v ty₂ body₂)
  | app_congr {f₁ f₂ a₁ a₂} : f₁ =β f₂ → a₁ =β a₂ → BetaEquivCases (f₁.app a₁) (f₂.app a₂)
  | beta {v ty body a t} : BetaEquivCases t (body.moveOutOfBinder v.toVar a)
    → BetaEquivCases t (.app (.lam v ty body) a)

@[symm]
private theorem BetaEquivCases_symm {t₁ t₂} : BetaEquivCases t₁ t₂ → BetaEquivCases t₂ t₁ := by
  intro h
  induction h
  case refl => exact .refl
  case binder_congr k v ty₁ ty₂ body₁ body₂ h_ty h_body =>

  case binder_congr k v ty₁ ty₂ body₁ body₂ h_ty h_body ih =>
    exact .binder_congr h_ty.symm h_body.symm
  case app_congr f₁ f₂ a₁ a₂ h_f h_a ih =>
    exact .app_congr h_f.symm h_a.symm
  case beta v ty body a t ih =>
    exact .beta ih

private theorem BetaEquivCases_of_BetaEquiv {t₁ t₂}
: t₁ =β t₂ → BetaEquivCases t₁ t₂ := by
  intro h
  induction h
  case beta t v ty body a reduced h ih => exact .beta ih
  case refl => exact .refl
  case symm t₁ t₂ h ih =>

  case refl t =>
    cases t
    case app => exact True.intro
    case binder k v ty body => left; exists ty, body
    all_goals left; rfl
  case symm t₁ t₂ h ih =>
    cases t₁
    case app f a =>
      have : ∃ f' a', f.app a = .app f' a' := by exists f, a
      split <;> first | right; exact this | trivial
    case binder k v ty body =>
      rcases ih with ⟨ty', body', h_eq⟩ | ⟨f, a, h_eq⟩
      · subst h_eq; left; exists ty, body
      · subst h_eq; exact True.intro
    all_goals
      rcases ih with h_eq | ⟨f, a, h_eq⟩
      · subst h_eq; left; rfl
      · subst h_eq; exact True.intro
  case trans t₁ t₂ t₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
    cases t₁
    case app f a => exact True.intro
    case binder k v ty body =>
      show (∃ ty' body', t₃ = .binder k v ty' body') ∨ (∃ f a, t₃ = .app f a)
      change _ ∨ _ at ih₁₂
      rcases ih₁₂ with ⟨ty', body', h_eq⟩ | ⟨f, a, h_eq⟩ <;> subst h_eq
      · exact ih₂₃
      · clear ih₂₃
        cases t₃
        case binder k' v' ty'' body'' =>
          left
          exists ty'', body''
          simp
          sorry
        all_goals simp


@[grind]
theorem binder_nequiv_prop_type_var {k v ty body t}
: .binder k v ty body =β t → t ≠ .prop ∧ t ≠ .type ∧ ∀ v, t ≠ .var v := by
  intro h
  set b := Term.binder k v ty body with h_b
  induction h
  apply Term.BetaEquiv.rec (motive := fun
    | .binder k v ty body, t | t, .binder k v ty body => t ≠ .prop ∧ t ≠ .type ∧ ∀ v, t ≠ .var v
    | _, _ => True)
  case beta =>
    -- The binder will never look like a beta application
    intro v ty body a
    set rhs := body.moveOutOfBinder v.toVar a with h_rhs
    generalize h_rhs : body.moveOutOfBinder v.toVar a = rhs
    cases rhs
    case binder => simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, and_self]
    all_goals trivial
  case refl =>
    intro t
    cases t
    case binder => simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, and_self]
    all_goals trivial
  case symm =>
    intro t₁ t₂ h ih
    cases t₁ <;> cases t₂
    case binder.binder => simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, and_self]
    all_goals trivial
  case trans =>
    intro t₁ t₂ t₃ h₁ h₂ ih₁ ih₂
    cases t₁ <;> cases t₃
    case binder.binder => simp only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, and_self]
    case binder.type =>
      exfalso
      simp at ih₁
      simp at ih₂
    all_goals try simp_all
    · simp_all

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
