module

namespace Jrlean

public abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

@[grind, expose]
public def Relation.rev (r : Relation α β) : Relation β α := fun b a => r a b

@[simp, grind =]
public theorem rev_rev (r : Relation α β) : r.rev.rev = r := by grind only [Relation.rev]
