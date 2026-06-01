class IMonad (m : (Index : Type) → (α : Index → Type) → Type) where
  pure {Index} {α : Index → Type} : (∀ i, α i) → m Index α
  bind {I} {α : I → Type} {β : I → I → Type}
  : (f : ∀ i, α i → m I (β i)) → m I α → m I ((i : _) × β i ·)


def IReader (State : Type u) (α : State → Type v) : Type (max u v) :=
  (s : State) → α s

namespace IReader

def pure {σ} {α : σ → _} (x : ∀ s, α s) : IReader σ (fun s => α s) := x
def read {σ} : IReader σ (fun s => { s' // s' = s}) := fun s => ⟨s, rfl⟩
def bind {σ} {α β : σ → _} (f : ∀ {s}, α s → IReader σ β) (x : IReader σ α)
: IReader σ β :=
  fun s => f (x s) s

/-

example : IReader Bool (fun b => if b then Nat else String) :=
  fun b => if h : b then cast 0 else ""

end IReader

def IState State (α : State → Type) :=
  (s : State) → α s × State

namespace IState

def pure : 

end IState

instance : IMonad IReader where
  pure x := fun s => x s
  bind f x := fun state => f state (x state) state

instance : IMonad IState where
  pure x := fun s => (x s, s)
  bind f x := fun s =>
    -- First do x.
    let (a, s') := x s
    -- Now do f x.
    let y := f s a
    y s'

-/
