module

import Jrlean.Of

namespace Jrlean

@[expose, reducible, coe_decl] public def coe {α β} (a : α) [CoeT α a β] : β := a
@[expose, reducible, coe_decl] public def coeAs {α} (β) (a : α) [CoeT α a β] : β := a

example (x : Nat) : Int := coe x

@[expose, reducible, coe_decl] public def cast {α β} (x : α) (h : α = β := by grind) : β := h.mp x
@[expose, reducible, coe_decl] public def castAs {α} (β) (x : α) (h : α = β := by grind) : β := h.mp x

example (n : Nat) : Vector Nat 0 :=
  cast (Vector.range (n - n))

@[expose] public section

/--
Just like `CoeOTC` is the `CoeOut* Coe*`, this class is `CoeOut*`.
-/
public class CoeOTC' (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeOTC'.coe

-- Reflexivity
instance {α} : CoeOTC' α α where coe := id
-- Cons
instance {α β γ} [i₁ : CoeOut α β] [i₂ : CoeOTC' β γ] : CoeOTC' α γ where coe a := i₂.coe of i₁.coe a

/--
Just like `CoeHTC` is the `CoeHead? CoeOut* Coe*`, this class is `CoeHead? CoeOut*`.
-/
class CoeHOTC (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeHOTC.coe

-- Without Head
instance {α β} [i : CoeOTC' α β] : CoeHOTC α β where coe := i.coe
-- With Head
instance {α β γ} [i₁ : CoeHead α β] [i₂ : CoeOTC' β γ] : CoeHOTC α γ where coe a := i₂.coe of i₁.coe a
-- Also allow a coersion just from this!
instance (priority:=low) {α β a} [i : CoeHOTC α β] : CoeT α a β where coe := i.coe a

/--
info: fun α β γ δ x x_1 x_2 =>
  inferInstance : (α : Sort u_1) →
  (β : Sort u_2) → (γ : Sort u_3) → (δ : Sort u_4) → CoeOut α β → CoeOut β γ → CoeOut γ δ → CoeOTC' α δ
-/
#guard_msgs in
#check fun (α β γ δ) (_ : CoeOut α β) (_ : CoeOut β γ) (_ : CoeOut γ δ) =>
  (inferInstance : CoeOTC' α δ)
