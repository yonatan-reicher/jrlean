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
  handle {a} : H → effect → Result a → Result a

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
    EffectHandler.handle handler msg (run handlers cont)

--- The crashing effect
structure Crash
def crash : Crash := {}

structure CrashHandler
instance {m err} [MonadExcept err m] [Monad m] [Inhabited err]
: EffectHandler CrashHandler m Crash where
  handle _h _msg _cont := throw default

def div (x y : Nat) : Effect (· = Crash) Nat := do
  if y == 0 then
    .effect crash
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

#eval show IO Nat from
  Effect.run
    (effects := (· = Crash))
    (Handler := fun e =>
      have : e = Crash := by grind
      have : EffectHandler CrashHandler _ e.val := by rw [this]; infer_instance
      ⟨CrashHandler, this⟩)
    (handlers := fun _ => CrashHandler.mk)
    (div 10 5)

--- Print a value
structure Print where
  msg : String
def print (msg : String) : Print := ⟨msg⟩

structure PrintHandler
instance : EffectHandler PrintHandler IO Print where
  handle _h msg cont := do
    IO.println msg.msg
    cont

@[instance]
axiom decidable_eq : DecidableEq Type
@[simp]
axiom neq : Crash != Print

#eval show IO Nat from
  Effect.run
    (effects := fun e => e = Crash ∨ e = Print)
    (Handler := fun e =>
      if h : e = Crash then
        have : EffectHandler CrashHandler _ e := by rw [h]; infer_instance
        ⟨CrashHandler, this⟩
      else
        have h : e = Print := by grind
        have : EffectHandler PrintHandler _ e := by rw [h]; infer_instance
        ⟨PrintHandler, this⟩
      )
    (handlers := fun e =>
      if h_crash : e = Crash then by simp [*]; exact CrashHandler.mk
      else by simp_all; exact PrintHandler.mk
      )
    do
      .effect $ print "Hello, world!"
      .effect $ print "This is an effect handler example."
      .effect crash
      return 42

end Jrlean
