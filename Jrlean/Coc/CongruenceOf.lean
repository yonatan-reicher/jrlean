module

public import Jrlean.Coc.Basic
public import Jrlean.Relation

namespace Jrlean.Coc.Term

public section

/-- Extends a relation to a congruence relation. A congruence relation is an equivalence relation
  that is preserved under application of functions and binders. -/
@[grind]
inductive CongruenceOf [varKind : VarKind] (f : Relation Term) : Relation Term
  | of {x y} : f x y → CongruenceOf f x y
  | refl {x} : CongruenceOf f x x
  | symm {x y} : CongruenceOf f x y → CongruenceOf f y x
  | trans {x y z} : CongruenceOf f x y → CongruenceOf f y z → CongruenceOf f x z
  | app {f₁ f₂ a₁ a₂} : CongruenceOf f f₁ f₂ → CongruenceOf f a₁ a₂
  → CongruenceOf f (app f₁ a₁) (app f₂ a₂)
  | binder {k v ty₁ ty₂ body₁ body₂} : CongruenceOf f ty₁ ty₂ → CongruenceOf f body₁ body₂
  → CongruenceOf f (binder k v ty₁ body₁) (binder k v ty₂ body₂)

variable [VarKind] {f : Relation Term}

instance : Std.Refl (CongruenceOf f) where refl _ := .refl
instance : Std.Symm (CongruenceOf f) where symm _ _ := .symm
instance : Trans (CongruenceOf f) (CongruenceOf f) (CongruenceOf f) where trans := .trans

@[refl]
theorem CongruenceOf_refl {x} : CongruenceOf f x x := .refl

theorem Equivalence_CongruenceOf : Equivalence (CongruenceOf f) where
  refl _ := .refl
  symm := .symm
  trans := .trans
