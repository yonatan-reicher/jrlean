module

namespace Jrlean

public abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

variable {α β}
variable {a : α} {b : β}
variable {r : Relation α β}

@[grind, expose]
public def Relation.rev (r : Relation α β) : Relation β α := fun b a => r a b

namespace Relation

section Refl

variable {r : Relation α α}

@[refl]
public theorem refl [Std.Refl r] : ∀ a, r a a := Std.Refl.refl

public instance rev_refl [Std.Refl r] : Std.Refl r.rev where
  refl := by
    intro a
    unfold rev
    rfl

end Refl

@[simp, grind =]
public theorem rev_rev : r.rev.rev = r := by grind only [Relation.rev]

@[simp, grind =]
public theorem rev_eq : r.rev b a = r a b := rfl
