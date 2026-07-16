module

public import Jrlean.Coc.Beta
public import Jrlean.SetTactic

namespace Jrlean.Coc.Term

@[elab_as_elim]
public theorem betaHeadInduction
[VarKind]
{motive : Term → Prop}
(prop : motive prop)
(type : motive type)
(var : ∀ v, motive (var v))
(binder : ∀ k v ty body, motive ty → motive body → motive (binder k v ty body))
(app : ∀ f a, betaHead (app f a) = none → motive f → motive a → motive (app f a))
(betaHead : ∀ v ty body arg, motive ty → motive body → motive (.app (lam v ty body) arg))
t
: motive t := by
  -- To prove the goal, we need induction, but over a stronger proposition
  suffices motive t ×' match t with
    -- we carry the proof of the inductive hypothesis of the type and body too
    | .binder k v ty body => motive ty ×' motive body
    | _ => PUnit from this.1
  induction t
  -- Cases where t is prop, type or var are very simple.
  iterate 3 constructor; apply_assumption; exact .unit
  -- In the binder case, we carry the inductive hypotheses
  case binder k v ty body ih_ty ih_body =>
    exact ⟨binder k v ty body ih_ty.1 ih_body.1, ih_ty.1, ih_body.1⟩
  -- In the application case, we match on the lhs, and if it's a function, we use the betaHead
  -- lemma to solve it, otherwise we use the app case.
  case app f a ih_f ih_a =>
    -- Just need to prove the induction hypothesis, nothing else
    suffices motive (.app f a) from ⟨this, .unit⟩
    -- Clean the context
    clear binder type prop var
    cases f
    case' binder k v ty body =>
      cases k
      case lam =>
        -- This is the only case where we have a beta head
        obtain ⟨_, ih_ty, ih_body⟩ := ih_f
        exact betaHead v ty body a ih_ty ih_body
    -- In all other, regular recursion
    all_goals apply app _ a rfl ih_f.1 ih_a.1

@[elab_as_elim]
public theorem betaHeadInduction'
[VarKind]
{motive : Term → Prop}
(prop : motive prop)
(type : motive type)
(var : ∀ v, motive (var v))
(binder : ∀ k v ty body, motive ty → motive body → motive (binder k v ty body))
(app : ∀ f a, betaHead (app f a) = none → motive f → motive a → motive (app f a))
(betaHead : ∀ v ty body arg, motive (body.moveOutOfBinder v.toVar arg)
  → motive (.app (lam v ty body) arg))
t
: motive t := by
  -- To prove the goal, we need induction, but over a stronger proposition
  suffices motive t ×' match t with
    -- we carry the proof of the inductive hypothesis of the type and body too
    | .binder k v ty body => motive ty ×' motive body
    | _ => PUnit from this.1
  induction t
  -- Cases where t is prop, type or var are very simple.
  iterate 3 constructor; apply_assumption; exact .unit
  -- In the binder case, we carry the inductive hypotheses
  case binder k v ty body ih_ty ih_body =>
    exact ⟨binder k v ty body ih_ty.1 ih_body.1, ih_ty.1, ih_body.1⟩
  -- In the application case, we match on the lhs, and if it's a function, we use the betaHead
  -- lemma to solve it, otherwise we use the app case.
  case app f a ih_f ih_a =>
    -- Just need to prove the induction hypothesis, nothing else
    suffices motive (.app f a) from ⟨this, .unit⟩
    -- Clean the context
    clear binder type prop var
    cases f
    case' binder k v ty body =>
      cases k
      case lam =>
        -- This is the only case where we have a beta head
        obtain ⟨_, ih_ty, ih_body⟩ := ih_f
        exact betaHead v ty body a ih_ty ih_body
    -- In all other, regular recursion
    all_goals apply app _ a rfl ih_f.1 ih_a.1

Jrlean.Coc.Term.BetaEquiv.recOn
[varKind : VarKind]
{motive : (a a_1 : Term) → a =β a_1 → Prop}
{a✝ a✝¹ : Term}
(t : a✝ =β a✝¹)
(beta : ∀ {x : VarDecl} {ty body arg : Term}, motive ((lam x ty body).app arg) (body.moveOutOfBinder x.toVar arg) ⋯)
(refl : ∀ {t : Term}, motive t t ⋯) (symm : ∀ {t₁ t₂ : Term} (a : t₁ =β t₂), motive t₁ t₂ a → motive t₂ t₁ ⋯)
(trans : ∀ {t₁ t₂ t₃ : Term} (a : t₁ =β t₂) (a_1 : t₂ =β t₃), motive t₁ t₂ a → motive t₂ t₃ a_1 → motive t₁ t₃ ⋯)
(app_congr :
  ∀ {f₁ f₂ a₁ a₂ : Term} (a : f₁ =β f₂) (a_1 : a₁ =β a₂),
    motive f₁ f₂ a → motive a₁ a₂ a_1 → motive (f₁.app a₁) (f₂.app a₂) ⋯)
(binder_congr :
  ∀ {k : BinderKind} {v : VarDecl} {ty₁ ty₂ body₁ body₂ : Term} (a : ty₁ =β ty₂) (a_1 : body₁ =β body₂),
    motive ty₁ ty₂ a → motive body₁ body₂ a_1 → motive (binder k v ty₁ body₁) (binder k v ty₂ body₂) ⋯) :
motive a✝ a✝¹ t

@[elab_as_elim]
public theorem inductionWithoutTrans
[VarKind]
{motive : Term → Term → Prop}
(t₁ t₂ : Term)
(h_equiv : t₁ =β t₂)
(beta : ∀ v ty t₁ t₂ arg, motive t₁ t₂ → motive (.app (.lam v ty t₁) arg) (t₁.moveOutOfBinder v.toVar arg))
(refl : ∀ t, motive t t)
(symm : ∀ t₁ t₂, motive t₁ t₂ → motive t₂ t₁)
(app : ∀ f₁ f₂ a₁ a₂, motive f₁ f₂ → motive a₁ a₂ → motive (.app f₁ a₁) (.app f₂ a₂))
(binder : ∀ k v ty₁ ty₂ body₁ body₂, motive ty₁ ty₂ → motive body₁ body₂
  → motive (.binder k v ty₁ body₁) (.binder k v ty₂ body₂))
: motive t₁ t₂ := by
  suffices motive t₁ t₂ ∧ ∀ t₃, (motive t₂ t₃ → motive t₁ t₃) ∧ (motive t₁ t₃ → motive t₂ t₃)
  from this.1
  induction h_equiv
  case beta v ty body arg =>
    apply And.intro
    · apply beta (t₁:=body) (t₂:=body)
      apply refl
    · intro t₃
      apply And.intro
      · intro h_t₃
        induction t₃
        case type => 
  case refl => apply refl
  case symm => apply symm; assumption
  case trans t₁ t₂ t₃ h₁ h₂ ih₁ ih₂ =>

