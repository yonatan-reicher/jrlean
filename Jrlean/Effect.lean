module

meta import Lean
public import Lean.Elab.Command

/-
An implementation of Algebraic Effects.
This is a monad called Effects which is indexed by a set of possible effects.
The effects themselves are instances of the Effect type. Effects can be sent and
then handled by handlers, which react accordingly and may alter the control
flow.

Actually, I had trouble implementing the concept of an effect handler because it
required predicating on type equality, and we cannot do that. For now, instead
of effect handlers, the effects themselves define generic translations to
monads.
-/

namespace Jrlean

-- Let's implement a set type as a predicate instead of importing mathlib...
private abbrev Set (t : Type u) := t → Prop
-- private instance {t : Type u} : CoeSort (Set t) (Type u) where
--   coe s := { x // s x }
-- set_option checkBinderAnnotations false in
-- private instance {X} {x : X} {p : X → Prop} [p x]
-- : ∀ x' : { x' // x' = x}, p x' := by grind

/-- An effect is a thing which passes messages to a handler, which then
    translates them into actions. -/
structure Effect where
  name : Lean.Name
  Input : Type
  Output : Type

open Lean.Parser.Term in
/--
The syntax for defining effects.

Example:
```lean
effect crash where
  Input := Unit
  Output := Empty
```
-/
syntax declModifiers " effect " ident (ident <|> hole <|> bracketedBinder)* declVal : command

-- Semantics of the `effect` command.
open Lean Parser.Term Elab.Command in
elab_rules : command
  | `(command|
    $mods:declModifiers
    effect $declId $params* where
      $[$fields:ident := $values]*
    ) => do
    -- Mess with the name
    let name := declId.getId
    let currNamespace ← getCurrNamespace
    let fullName := currNamespace ++ name
    -- Now fields
    let fieldSets ←
      fields.zip values
      |>.mapM fun (field, value) => `(structInstField| $field:ident := $value)
    -- Translate to syntax and run.
    elabCommand <| ← `(
      $mods:declModifiers
      def $declId $params* : Effect where
        name := $(quote fullName)
        $fieldSets*
    )

/-- Instanced for monads and effects that can be translated into those monads.
-/
class EffectResult (e : Effect) (result : Type → Type u) where
  translate {α} : e.Input → (e.Output → result α) → result α

/-- The effects monad has the ability to apply send effects to handlers. -/
inductive Effects (effects : Set Effect) (a : Type) where
  | pure : a → Effects effects a
  | effectThen
    (e : Effect)
    (inp : e.Input)
    (cont : e.Output → Effects effects a)
    (h_effect : effects e := by grind)
    : Effects effects a

def Effects.effect
  {effects}
  (e : Effect)
  (inp : e.Input)
  (h_effect : effects e := by grind)
  : Effects effects e.Output :=
  .effectThen e inp .pure

instance {effects} : Monad (Effects effects) where
  pure := .pure
  bind := bind -- defined separately for recursion
where
  bind {α β} (x : Effects effects α) (f : α → Effects effects β) :=
    match x with
    | .pure a => f a
    | .effectThen e inp y h => .effectThen e inp fun out => bind (y out) f

def Effects.run
  {α}
  {effects : Set Effect}
  {Result} [Pure Result]
  (x : Effects effects α)
  (h_effect_result : ∀ e, effects e → EffectResult e Result := by simp_all)
  : Result α :=
  match x with
  | .pure a => Pure.pure a
  | .effectThen e inp cont h =>
    have : EffectResult e Result := h_effect_result e h
    EffectResult.translate inp fun out => run (cont out) h_effect_result

/-- The crashing effect. -/
effect crash where
  Input := Unit
  Output := Empty

-- Any monad that can throw an error which has a default value can run crash
-- effects.
instance {m err} [MonadExcept err m] [Inhabited err]
: EffectResult crash m where
  translate _msg _cont := throw default

def div (x y : Nat) : Effects (· = crash) Nat := do
  if y == 0 then
    let empty ← .effect crash ()
    empty.elim
  else
    return (x / y)

#eval show Option Nat from
  Effects.run
    (effects := (· = crash))
    (div 10 0)
    $ by
      intros e h_eq
      subst h_eq
      infer_instance

#eval show IO Nat from
  Effects.run
    (effects := (· = crash))
    (div 10 5)
    $ by
      intros e h_eq
      subst_vars
      infer_instance

/-- Print a value. -/
def Print : Effect where
  name := `Print
  Input := String
  Output := Unit

instance : EffectResult Print IO where
  translate msg cont := do
    IO.println $ show String from msg
    cont ()

#eval show IO Nat from
  Effects.run
    (effects := fun e => e = crash ∨ e = Print)
    (do
      .effect Print "Hello, world!"
      .effect Print "This is an effect handler example."
      let empty ← .effect crash ()
      empty.elim)
    $ by
      intros e h
      if h_name_eq_crash : e.name = crash.name then
        have : e = crash := by grind [crash, Print]
        subst_vars
        infer_instance
      else
        have h_print : e = Print := by grind
        subst h_print
        infer_instance

@[reducible]
effect ask (Input Output : Type) where
  Input := Input
  Output := Output

instance {Inp Out m} [Monad m] [MonadReader (Inp → Out) m] : EffectResult (ask Inp Out) m where
    translate inp cont := do
      let out := (← read) inp
      cont out

#eval (ReaderT.run (m := Id) · fun x => x + 1)
  <| Effects.run
    (effects := fun e => e = ask Nat Nat)
    (do
      let x ← .effect (ask Nat Nat) 9
      return x * x)
    $ by
      intros
      subst_vars
      infer_instance

end Jrlean
