module

namespace Jrlean

public section

/-- A version of StateT where the return can be indexed by the current state. -/
@[expose]
def StateT (σ1 : Type _) (σ2 : Type _) (m : Type _ → Type _) (α : σ1 → Type _)
: Type _ :=
  (s : σ1) → m (α s × σ2)

def StateT.run {σ1 σ2 m α} (s : σ1) (x : StateT σ1 σ2 m α) : m (α s × σ2) :=
  x s

def StateT.pure {σ m α} [Pure m] (a : ∀ s, α s) : StateT σ σ m α :=
  fun s => Pure.pure (a s, s)

def StateT.map {σ1 σ2 m α β} [Functor m] (f : ∀ s, α s → β s)
: StateT σ1 σ2 m α → StateT σ1 σ2 m β
  | x => fun s => x s |> Functor.map fun (a, s') => (f s a, s')

-- def StateT.bind
-- {σ1 : Type} {σ2 : Type} {σ3 : Type}
-- {m : Type → Type}
-- {α : σ1 → Type} {β : σ2 → Type}
-- (f : ∀ s, α s → StateT σ2 σ3 m β)
-- (x : StateT σ1 σ2 m α)
-- : StateT σ1 σ3 m (fun s1 => let s2 := (x.run s1).2; β s2)
--   | x => fun s => sorry
