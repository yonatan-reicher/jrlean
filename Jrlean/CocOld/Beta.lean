module

public import Jrlean.Coc.Basic
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Relation
import Jrlean.SetTactic
import Jrlean.ByContra

namespace Jrlean.Coc.Term

public section

variable [varKind : VarKind]

@[expose, grind, simp]
def betaHead : Term → Option Term
  | app (lam x _ body) arg => some (body.moveOutOfBinder x.toVar arg)
  | _ => none

inductive BetaEquiv : Relation Term
  | beta {x ty body arg} : BetaEquiv (app (lam x ty body) arg) (body.moveOutOfBinder x.toVar arg)
  | refl {t} : BetaEquiv t t
  | symm {t₁ t₂} : BetaEquiv t₁ t₂ → BetaEquiv t₂ t₁
  | trans {t₁ t₂ t₃} : BetaEquiv t₁ t₂ → BetaEquiv t₂ t₃ → BetaEquiv t₁ t₃
  | app_congr {f₁ f₂ a₁ a₂} : BetaEquiv f₁ f₂ → BetaEquiv a₁ a₂ → BetaEquiv (app f₁ a₁) (app f₂ a₂)
  | binder_congr {k v ty₁ ty₂ body₁ body₂} : BetaEquiv ty₁ ty₂ → BetaEquiv body₁ body₂
    → BetaEquiv (binder k v ty₁ body₁) (binder k v ty₂ body₂)

infix:50 " =β " => BetaEquiv

abbrev BetaNEquiv a b := ¬(a =β b)
infix:50 " ≠β " => BetaNEquiv

@[refl, simp, grind .] theorem BetaEquiv_refl {t} : t =β t := .refl
@[symm, grind →] theorem BetaEquiv_symm {t₁ t₂} : t₁ =β t₂ → t₂ =β t₁ := .symm
@[grind →] theorem BetaEquiv_trans {t₁ t₂ t₃} : t₁ =β t₂ → t₂ =β t₃ → t₁ =β t₃ := .trans

instance : Std.Refl BetaEquiv where refl _ := BetaEquiv_refl
instance : Std.Symm BetaEquiv where symm _ _ := BetaEquiv_symm
instance : Trans BetaEquiv BetaEquiv BetaEquiv where trans := BetaEquiv_trans

theorem Equivalence_BetaEquiv : Equivalence BetaEquiv where
  refl _ := BetaEquiv_refl
  symm := BetaEquiv_symm
  trans := BetaEquiv_trans

instance : Setoid Term where
  r := BetaEquiv
  iseqv := Equivalence_BetaEquiv

-- @[induction_eliminator, elab_as_elim]
-- theorem leftInduction
-- {motive : Term → Prop}
-- (beta : ∀ {v ty body arg}, motive (body.moveOutOfBinder v.toVar arg)
--   → motive (app (lam v ty body) arg))
-- (refl : ∀ {t}, motive t)
-- (symm : ∀ {t₁ t₂}, t₁ =β t₂ → motive t₁ → motive t₂)
-- -- (trans : ∀ {t₁ t₂ t₃}, t₁ =β t₂ → t₂ =β t₃ → motive t₁ → 
-- (app_congr : ∀ {f₁ f₂ a₁ a₂}, f₁ =β f₂ → a₁ =β a₂ → motive f₁ → motive f₂ → motive a₁ → motive a₂
--   → motive (app f₁ a₁))
-- : ∀ {t}, motive t := by
--   induction
--   sorry

@[expose]
partial def betaReduce (t : Term) : Term :=
  match t with
  | type | prop | var .. => t
  | app f a =>
    let f := betaReduce f
    let a := betaReduce a
    match betaHead (app f a) with
    | some t => betaReduce t
    | none => app f a
  | binder k v ty body =>
    binder k v (betaReduce ty) (betaReduce body)
