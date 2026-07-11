module

public import Jrlean.Coc.Basic
public import Jrlean.Coc.MoveIntoOutOf
public import Jrlean.Coc.CongruenceOf
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

def BetaEquiv : Relation Term := sorry

infix:50 " =β " => BetaEquiv

abbrev BetaNEquiv a b := ¬(a =β b)
infix:50 " ≠β " => BetaNEquiv

@[refl, simp, grind .] theorem BetaEquiv_refl {t} : t =β t := sorry
@[symm, grind →] theorem BetaEquiv_symm {t₁ t₂} : t₁ =β t₂ → t₂ =β t₁ := sorry
@[grind →] theorem BetaEquiv_trans {t₁ t₂ t₃} : t₁ =β t₂ → t₂ =β t₃ → t₁ =β t₃ := sorry

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

