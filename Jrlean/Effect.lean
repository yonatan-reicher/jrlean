module

import Jrlean.CollectionLemmas
import Std
meta import Lean
public import Jrlean.HasTypeId
public import Jrlean.TypeWithId
public import Lean.Elab.Command
public meta import Jrlean.HasTypeId

/-
An implementation of Algebraic Effects.
This is a monad called Effects which is indexed by a set of possible effects.
The effects themselves are structures that have input and output types, and they
can be defined using the `effect` command. Effects can be sent and then handled
by handlers, which react accordingly and may alter the control flow.

TODO: Implement the concept of an effect handler.
For now, instead of effect handlers, the effects themselves define generic
translations to monads.
-/

namespace Jrlean

-- Let's implement a set type as a predicate instead of importing mathlib...
private abbrev Set (t : Type u) [BEq t] [Hashable t] := Std.ExtHashSet t
-- private instance {t : Type u} : CoeSort (Set t) (Type u) where
--   coe s := { x // s x }
-- set_option checkBinderAnnotations false in
-- private instance {X} {x : X} {p : X → Prop} [p x]
-- : ∀ x' : { x' // x' = x}, p x' := by grind

/-- An effect is a thing which passes messages to a handler, which then
    translates them into actions. -/
@[ext]
structure Effect where
  name : Lean.Name
  InputWithId : TypeWithId
  OutputWithId : TypeWithId
  deriving DecidableEq, Hashable, Repr

@[reducible] def Effect.Input (e : Effect) : Type := e.InputWithId
@[reducible] def Effect.Output (e : Effect) : Type := e.OutputWithId

section Meta

open Lean Elab Term Command
open Lean.Parser.Term

public syntax effectField := ident " := " term

/--
The syntax for defining effects.

Example:
```lean
effect crash ↦ Empty where
  reason : String
```
-/
public syntax effectDecl :=
  withPosition(declModifiers)
  "effect " ident (ident <|> hole <|> bracketedBinder)* " where "
    manyIndent(effectField)

syntax effectDecl : command

structure EffectBuilderState where
  input : List Term
  output : List Term
  badFields : List (Name × Term)

-- Semantics of the `effect` command.
elab_rules : command
  | `(command|
    $mods:declModifiers
    effect $declId $params:ident* where
      $fields*
  ) => do
    let s : EffectBuilderState := {
      input := []
      output := []
      badFields := []
    }
    let s ← fields.foldlM (init := s) fun s (field : TSyntax ``effectField) => do
      match field with
      | `(effectField| $name:ident := $t:term) =>
        let name := name.getId
        if name == .mkSimple "Input" then
          pure { s with input := t :: s.input }
        else if name == .mkSimple "Output" then
          pure { s with output := t :: s.output }
        else
          pure { s with badFields := (name, t) :: s.badFields }
      | _ => panic! "invalid syntax in effect fields: {field}"
    let input ←
      match s.input with
      | [t] => pure t
      | [] => throwError m!"Effect '{declId}' is missing an 'Input' field."
      | _ => throwError m!"Effect '{declId}' has multiple 'Input' fields."
    let output ←
      match s.output with
      | [t] => pure t
      | [] => throwError m!"Effect '{declId}' is missing an 'Output' field."
      | _ => throwError m!"Effect '{declId}' has multiple 'Output' fields."
    for (name, _) in s.badFields do
      throwError m!"Effect '{declId}' has an unrecognized field '{name}'."
    elabCommand <| ← `(
      $mods:declModifiers
      def $declId $params* : Effect where
        name := $(quote declId.getId)
        InputWithId := .mk ($input)
        OutputWithId := .mk ($output)
    )

end Meta

/-- Instanced for monads and effects that can be translated into those monads.
-/
class EffectResult (e : Effect) (result : Type → Type u) where
  translate {α} : e.Input → (Effect.Output e → result α) → result α

/-- The effects monad has the ability to apply send effects to handlers. -/
inductive Effects (effects : Set Effect) (a : Type) where
  | pure : a → Effects effects a
  | effectThen
    (e : Effect)
    (inp : e.Input)
    (cont : Effect.Output e → Effects effects a)
    (h_effect : e ∈ effects := by grind)

def Effects.effect
  {effects}
  (e : Effect)
  (inp : e.Input)
  (h_effect : e ∈ effects := by grind)
  : Effects effects (Effect.Output e) :=
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
  (h_effect_result : ∀ e ∈ effects, EffectResult e Result := by simp_all)
  : Result α :=
  match x with
  | .pure a => Pure.pure a
  | Effects.effectThen e inp cont h =>
    have : EffectResult e Result := h_effect_result e h
    EffectResult.translate inp fun out => run (cont out) h_effect_result

/-- The crashing effect. -/
effect Crash where
  Input := Unit
  Output := Empty

-- Any monad that can throw an error which has a default value can run crash
-- effects.
instance {m err} [MonadExcept err m] [Inhabited err]
: EffectResult Crash m where
  translate _msg _cont := throw default

def div (x y : Nat) : Effects {Crash} Nat := do
  if y == 0 then
    let empty ← .effect Crash ()
    empty.elim
  else
    return (x / y)

/-- info: none -/
#guard_msgs in
#eval show Option Nat from
  Effects.run
    (effects := {Crash})
    (div 10 0)
    $ by
      intros e h_eq
      simp at h_eq
      subst e
      infer_instance

/-- info: 2 -/
#guard_msgs in
#eval show IO Nat from
  Effects.run
    (effects := {Crash})
    (div 10 5)
    $ by
      intros e h_eq
      simp at h_eq
      subst e
      infer_instance

/-- Print a value. -/
effect Print where
  Input := String
  Output := Unit

instance : EffectResult Print IO where
  translate msg cont := do
    IO.println $ show String from msg
    cont ()

/--
info: Hello, world!
This is an effect handler example.
---
error: (`Inhabited.default` for `IO.Error`)
-/
#guard_msgs in
#eval show IO Nat from
  Effects.run
    (effects := {Print, Crash})
    (do
      .effect Print "Hello, world!"
      .effect Print "This is an effect handler example."
      let empty ← .effect Crash ()
      empty.elim)
    $ by
      intros e h
      if h_name_eq_crash : e.name = Crash.name then
        have : e = Crash := by grind [Crash, Print]
        subst_vars
        infer_instance
      else
        have h_print : e = Print := by grind
        subst h_print
        infer_instance

@[reducible]
effect Ask (Input Output : Type) [HasTypeId Input] [HasTypeId Output] where
  Input := Input
  Output := Output

instance {Inp Out m} [HasTypeId Inp] [HasTypeId Out] [Monad m]
[MonadReader (Inp → Out) m] : EffectResult (Ask Inp Out) m where
  translate inp cont := do
    let out := (← read) inp
    cont out

/-- info: 100 -/
#guard_msgs in
#eval (ReaderT.run (m := Id) · fun x => x + 1)
  <| Effects.run
    (effects := {Ask Nat Nat})
    (do
      let x ← .effect (Ask Nat Nat) 9
      return x * x)
    $ by
      intro e h
      simp at h
      subst_vars
      infer_instance
