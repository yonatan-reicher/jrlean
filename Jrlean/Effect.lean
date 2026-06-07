module

/-
An implementation of Algebraic Effects.
This is a monad called Effect which is indexed by a set of possible effects.
The effects themselves are just types, and instances of them can be passed as
messages to an effect handler, which interprets them and reacts.
-/

namespace Jrlean

-- Let's implement a set type as a predicate instead of importing mathlib...
private abbrev Set (t : Type u) := t → Prop
private instance {t : Type u} : CoeSort (Set t) (Type u) where
  coe s := { x // s x }
set_option checkBinderAnnotations false in
private instance {X} {x : X} {p : X → Prop} [p x]
: ∀ x' : { x' // x' = x}, p x' := by grind

--- The effect monad just stores the output
inductive Effect (effects : Set Type) (a : Type) where
  | pure : a → Effect effects a
  | effectThen {e : { e // effects e } } : ↑e → Effect effects a → Effect effects a

def Effect.effect {effects e} (msg : e) (h_mem : effects e := by grind)
: Effect effects Unit :=
  .effectThen (e := ⟨e, h_mem⟩) msg (.pure ())

instance {effects} : Monad (Effect effects) where
  pure := .pure
  bind := bind -- defined separately for recursion
where
  bind {α β} (x : Effect effects α) (f : α → Effect effects β) :=
    match x with
    | .pure a => f a
    | .effectThen msg y => .effectThen msg (bind y f)

class EffectHandler H Result [Monad Result] effect where
  handle {effects a} : H → effect → Effect effects a → Result a

def Effect.run
  {α}
  {effects : Set Type}
  {Result}
  [Monad Result]
  {Handler : ∀ e : effects, (H : Type) × EffectHandler H Result e}
  (handlers : ∀ e, (Handler e).1)
  : Effect effects α → Result α
  | .pure a => return a
  | .effectThen (e := e) msg cont =>
    let handler := handlers e
    have := (Handler e).2
    EffectHandler.handle handler msg cont

--- The crashing effect
structure Crash
def crash : Crash := {}

structure CrashHandler
instance : EffectHandler CrashHandler Option Crash where
  handle _h _msg _cont := none

def div (x y : Nat) : Effect (· = Crash) Nat := do
  if y == 0 then
    Effect.effect crash
    return 0
  else
    return (x / y)

#eval show Option Nat from
  Effect.run
    (effects := (· = Crash))
    (Handler := fun e =>
      have : e = Crash := by grind
      have : EffectHandler CrashHandler _ e.val := by rw [this]; infer_instance
      ⟨CrashHandler, this⟩)
    (handlers := fun _ => CrashHandler.mk)
    (div 10 0)

#eval show Option Nat from
  Effect.run
    (effects := (· = Crash))
    (Handler := fun e =>
      have : e = Crash := by grind
      have : EffectHandler CrashHandler _ e.val := by rw [this]; infer_instance
      ⟨CrashHandler, this⟩)
    (handlers := fun _ => CrashHandler.mk)
    (div 10 5)

end Jrlean
