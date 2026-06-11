module

meta import Lean
public import Lean.Elab.Command

/-
An implementation of Algebraic Effects.
This is a monad called Effects which is indexed by a set of possible effects.
The effects themselves are types that implement the Effect typeclass, and they
can be defined using the `effect` command. Effects can be sent and then handled
by handlers, which react accordingly and may alter the control flow.

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
class Effect e extends TypeName e where
  Output : Type

instance (a b : Type) [Effect a] [Effect b] : Decidable (a = b) := by
  open TypeName (typeName) in
  constructor
  intro a_eq_b
  if h_name_eq : typeName a = typeName b then
    sorry
  else
    sorry

open Lean.Parser.Term in
/--
The syntax for defining effects.

Example:
```lean
effect crash ↦ Empty where
  reason : String
```
-/
syntax
  withPosition(declModifiers)
  "effect " ident (ident <|> hole <|> bracketedBinder)*
  ( " ↦ " term )?
  ( " where "
    (binderDefault <|> bracketedBinder)*
  )?
  : command

open Lean Elab Parser Term Command in
-- Semantics of the `effect` command.
elab_rules : command
  | `(command|
    $mods:declModifiers
    effect $declId $params:ident*
    $[↦ $output]?
    $[where $binders:binderDefault*]?
  ) => do
    let binders := binders.getD #[]
    let binders ← binders.mapM (fun b =>
      match b with
      | `(bracketedBinder| ($binder:ident : $type:term)) =>
        `(structSimpleBinder| $binder:ident : $type)
      | _ => do
        throwError m!"Cannot handle binder syntax")
     -- Check that the name is not already used.
    -- Translate to syntax and run.
    elabCommand <| ← `(
      $mods:declModifiers
      structure $declId $params* where
        $[$binders]*
      deriving TypeName, DecidableEq
      instance : Effect ($declId $params*) := .mk
        (Output := $(output.getD (mkIdent ``Unit)))
    )

/-- Instanced for monads and effects that can be translated into those monads.
-/
class EffectResult e [Effect e] (result : Type → Type u) where
  translate {α} : e → (Effect.Output e → result α) → result α

/-- The effects monad has the ability to apply send effects to handlers. -/
inductive Effects (effects : Set (Sigma Effect)) (a : Type) where
  | pure : a → Effects effects a
  | effectThen
    e
    [instEffect : Effect e]
    (inp : e)
    (cont : Effect.Output e → Effects effects a)
    (h_effect : effects ⟨e, instEffect⟩ := by grind)
    : Effects effects a

def Effects.effect
  {effects e}
  [instEffect : Effect e]
  (inp : e)
  (h_effect : effects ⟨e, instEffect⟩ := by grind)
  : Effects effects (Effect.Output e) :=
  .effectThen e inp .pure

instance {effects} : Monad (Effects effects) where
  pure := .pure
  bind := bind -- defined separately for recursion
where
  bind {α β} (x : Effects effects α) (f : α → Effects effects β) :=
    match x with
    | .pure a => f a
    | Effects.effectThen e inp y h => .effectThen e inp fun out => bind (y out) f

def Effects.run
  {α}
  {effects : Set (Sigma Effect)}
  {Result} [Pure Result]
  (x : Effects effects α)
  (h_effect_result : ∀ e, effects e → @EffectResult e.1 e.2 Result := by simp_all)
  : Result α :=
  match x with
  | .pure a => Pure.pure a
  | Effects.effectThen e inp cont h =>
    have : EffectResult e Result := h_effect_result ⟨e, inferInstance⟩ h
    EffectResult.translate inp fun out => run (cont out) h_effect_result

/-- The crashing effect. -/
effect Crash ↦ Empty

-- Any monad that can throw an error which has a default value can run crash
-- effects.
instance {m err} [MonadExcept err m] [Inhabited err]
: EffectResult Crash m where
  translate _msg _cont := throw default

def div (x y : Nat) : Effects (fun e => e = Crash) Nat := do
  if y == 0 then
    let empty ← .effect Crash.mk
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
