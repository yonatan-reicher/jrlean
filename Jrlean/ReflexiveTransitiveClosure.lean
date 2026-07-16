module

public import Jrlean.Relation
public import Jrlean.Subrelation
public import Jrlean.Assumption
meta import Lean

namespace Jrlean

public section

-- First let's start with defining names and notation

variable {α : Sort u}

@[grind]
inductive ReflTransClosure (r : Relation α α) : Relation α α where
| refl {a} : ReflTransClosure r a a
| leftCons : r a b → ReflTransClosure r b c → ReflTransClosure r a c

-- We also have the full name
abbrev ReflexiveTransitiveClosure (r : Relation α α) := ReflTransClosure r

postfix:max "*" => ReflTransClosure

-- Now let's define lemmas

namespace ReflTransClosure

variable {r : Relation α α}
variable {a b c : α}

section Refl

attribute [refl] refl

instance : Std.Refl r* where refl _ := refl

end Refl

section Trans

@[grind →, grind <=, grind .]
theorem trans : (r*) a b → (r*) b c → (r*) a c := by
  intro left right
  induction left <;> grind

@[grind .]
theorem rightCons : (r*) a b → r b c → (r*) a c := by grind

instance instTrans : Trans (r*) (r*) (r*) where trans := trans
instance instTransLeftCons : Trans r (r*) (r*) where trans := leftCons
instance instTransRightCons : Trans (r*) r (r*) where trans := rightCons

end Trans

section Symm

@[symm, grind .]
theorem symm_of_symm [Std.Symm r] : (r*) a b → (r*) b a := by
  intro h
  induction h
  case refl => trivial
  case leftCons a₁ a₂ b head tail ih =>
    replace head := Std.Symm.symm _ _ head
    grind

end Symm

@[grind →]
theorem eq_of_subrelation_of_subrelation {r₁ r₂ : Relation α α}
: r₁ ⊆ r₂ → r₂ ⊆ r₁* → r₂* = r₁* := by
  intro h₁ h₂
  symm
  two_directions
  case forward =>
    constructor; intro a b h_r₁_star
    show (r₂*) a b
    induction h_r₁_star <;> grind
  case backward =>
    constructor; intro a b h_r₂_star
    show (r₁*) a b
    induction h_r₂_star <;> grind

section Reverse

@[simp, grind =]
theorem rev_eq_rev : (r*).rev = r.rev* := by
  two_directions
  all_goals constructor; intro a b h
  case forward =>
    induction h
    case refl => trivial
    case leftCons => grind only [rightCons, = Relation.rev.eq_1]
  case backward =>
    induction h
    case refl => sorry
    case leftCons => grind only [= Relation.rev.eq_1, rightCons]

end Reverse

@[elab_as_elim]
theorem rightInduction
{motive : ∀ a b, (r*) a b → Prop}
(h : (r*) a b)
(refl : ∀ a, motive a a .refl)
(rightCons : ∀ (a b c : α) h₁ h₂, motive a b h₁ → motive a c (.rightCons h₁ h₂))
: motive a b h := by
  -- We construct the proof from the right using left induction by switching the order of the
  -- arguments and using left induction. In order to do that, we define an reversed relation.
  let r' := r.rev
  rename (r*) a b => h_old
  have h : (r'*) b a := by sorry
  -- Induction on the reversed proof of (r*)!
  induction h
  case refl a => apply refl
  case leftCons b₂ b₁ a head tail ih =>
    have : (r*) a b₁ := by sorry
    have : r b₁ b₂ := head
    have : motive a b₁ assumption := by sorry
    apply rightCons a b₁ b₂ <;> assumption

@[grind <=]
theorem singleton : r a b → (r*) a b := fun x => .leftCons x .refl
