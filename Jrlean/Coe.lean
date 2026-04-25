module

namespace Jrlean

@[expose, reducible] public def coe {α β} (a : α) [CoeT α a β] : β := a
@[expose, reducible] public def coeAs {α} (β) (a : α) [CoeT α a β] : β := a

example (x : Nat) : Int := coe x

@[expose, reducible] public def cast {α β} (x : α) (h : α = β := by grind) : β := h ▸ x
@[expose, reducible] public def castAs {α} (β) (x : α) (h : α = β := by grind) : β := h ▸ x

example (n : Nat) : Vector Nat 0 :=
  cast (Vector.range (n - n))

