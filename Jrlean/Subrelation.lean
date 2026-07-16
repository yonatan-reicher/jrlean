module

public import Jrlean.Relation

namespace Jrlean

public section

variable {α : Sort u} {β : Sort v}
variable {r r₁ r₂ r₃ : Relation α β}

/-- Is the left relation a subrelation of the right one? -/
@[grind]
class Relation.Subrelation (r₁ r₂ : Relation α β) where
  subsumption : ∀ a b, r₁ a b → r₂ a b

-- 50 is taken from '<='
infix:50 " ⊆ " => Relation.Subrelation

namespace Relation

theorem eq_of_subrelation_of_subrelation (forward : r₁ ⊆ r₂) (backward : r₂ ⊆ r₁) : r₁ = r₂ := by
  funext x
  grind

grind_pattern eq_of_subrelation_of_subrelation => r₁ ⊆ r₂, r₂ ⊆ r₁

macro "two_directions" : tactic => `(tactic|apply eq_of_subrelation_of_subrelation)
