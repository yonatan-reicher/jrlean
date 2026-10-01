module

namespace Jrlean

@[expose]
public section

/-!
Haskell's Arrow. These are things which have a concept of input and output and can be composed
together. They are a replacement for monads in certain cases.
-/
class Arrow (A : Type u → Type u → Type v) where
  ofFunc : (α → β) → A α β
  composeLeft : A β γ → A α β → A α γ
  first : A α β → A (α × γ) (β × γ)


variable {A : Type u → Type u → Type v} [Arrow A]

def Arrow.id : A α α := ofFunc λ x => x
def Arrow.composeRight : A α β → A β γ → A α γ := flip composeLeft

infixr:90 " ∘ "  => Arrow.composeLeft
infixr:min1 " <| "  => Arrow.composeLeft
infixl:min1 " |> "  => Arrow.composeRight

recommended_spelling "compose" for "∘" in [Arrow.composeLeft]

-- register_simp_attr arrow
-- attribute [arrow] Arrow.id
open Arrow in
attribute [simp, grind]
  ofFunc
  composeLeft composeLeft
  first -- second
  Arrow.id


abbrev Function α β := α → β

@[reducible]
instance : Arrow Function where
  ofFunc := id
  composeLeft := Function.comp
  first := (Prod.map · id)


open Arrow in
class LawfulArrow A [Arrow A] where
  id_compose (f : A α β) : id ∘ f = f
  compose_id (f : A α β) : f ∘ id = f

instance : LawfulArrow Function where
  id_compose _ := rfl
  compose_id _ := rfl


def Kleisli m [Monad m] α β := α → m β

instance [Monad m] : Arrow (Kleisli m) where
  ofFunc f a := f <$> pure a
  composeLeft g f a := g =<< f a
  first f := λ (a, c) => return (← f a, c)
