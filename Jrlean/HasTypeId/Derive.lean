module

public import Jrlean.HasTypeId.Basic
import Jrlean.TypeId
import Lean.Elab.Deriving
import Lean.Elab.Term.TermElabM
import Lean.LocalContext
import Lean.PrettyPrinter

namespace Jrlean

/- In this module, we describe a thing called a derive handler. This
   will allow us to add `deriving TypeId` to types. -/

open Lean Elab Command Core Meta
open Lean.Parser.Term (bracketedBinder)

local instance : ToFormat ConstantInfo where
  format
    | .inductInfo .. => "inductInfo"
    | .axiomInfo .. => "axiomInfo"
    | .defnInfo .. => "defnInfo"
    | .thmInfo .. => "thmInfo"
    | .opaqueInfo .. => "opaqueInfo"
    | .quotInfo .. => "quotInfo"
    | .ctorInfo .. => "ctorInfo"
    | .recInfo .. => "recInfo"

def _root_.Lean.Expr.toSyntax := Term.exprToSyntax

def generateNames (n : Nat) (suggestion : Name) : CoreM (Array Name) :=
  Array.range n
  |>.mapM fun i => mkFreshUserName (suggestion.appendAfter <| toString i)

/- A derive handler takes an array of names and elaborates commands that
   introduce the instance for them. We also need to add axioms that assume the
   behaviour we are adding is correct. This correctness cannot be proven inside
   Lean. This is because you can't question Lean on the name of a type. -/
def derivingHandler : DerivingHandler := fun names => do
  for (name : Name) in names do
    -- This only makes sense for constants (constants can also refer to
    -- functiosn and types) which are created by the command. This does not
    -- make sense for definitions. It also doesn't make sense for things
    -- which aren't types (example, different integer constants can be
    -- equal, different type constants can't be equal, instances of
    -- propositions are all equal).
    let constant_info ← getConstInfo name
    match constant_info with
    | .inductInfo inductiveVal => do
      let (params, ret) ← readParameters inductiveVal
      command name inductiveVal.levelParams params
    | .axiomInfo ..
    | .defnInfo ..
    | .thmInfo ..
    | .opaqueInfo ..
    | .quotInfo ..
    | .ctorInfo ..
    | .recInfo .. =>
      throwError m!"cannot derive TypeId for constant '{name}' as it is not definition of a new unique type. ConstantInfo object: {constant_info}"
  return true
where
  command (name : Name) levelParams (paramTypes : Array Expr) : CommandElabM Unit := do
    -- Filter the level parameters to only those that the parameter types depend
    -- on. This is because having universe levels that only affect the return
    -- type or nothing at all means a synthesis failure when we try to call the
    -- typeId function.
    -- let levelParams :=
    --   levelParams.filter fun l => paramTypes.any fun t =>
    --     dependsOn t l
    /-
    Does three things:
    1. declares a function called _.typeId
    2. declares an axiom _.typeId_ofType
    3. declares an instance of HasTypeId
    -/
    -- First generate some names for the arguments.
    let paramNames ← liftCoreM <| generateNames paramTypes.size `a
    -- An expression that returns the type `TypeId`
    let typeIdType : Expr := .const ``TypeId []
    -- An expression that returns the type `HasTypeId α`
    let hasTypeIdType α := mkAppM ``HasTypeId #[α]
    -- Declare the type id
    liftCoreM <| addDecl (forceExpose := true) <| .defnDecl {
      name := name ++ `typeId
      levelParams := levelParams
      type := ← liftTermElabM do
        -- Declare the parameters
        withLocalDeclsDND (paramNames.zip paramTypes) fun params => do
        -- Declare the instances
        withLocalDecls
          (params.map (fun p => (.anonymous, .instImplicit, fun _ => hasTypeIdType p)))
          fun paramInsts => do
        mkForallFVars
          (params.zip paramInsts |>.flatMap fun (a, b) => #[a, b])
          typeIdType
      value := ← liftTermElabM do -- TODO: This should take aruguments and match the type
        -- Declare the parameters
        withLocalDeclsDND (paramNames.zip paramTypes) fun params => do
        -- Declare the instances
        withLocalDecls
          (params.map (fun p => (.anonymous, .instImplicit, fun _ => hasTypeIdType p)))
          fun paramInsts => do
        mkLambdaFVars
          (params.zip paramInsts |>.flatMap fun (a, b) => #[a, b])
          <| ← mkAppM ``TypeId.mk #[
          -- First argument is the constant's name
          toExpr name,
          -- The rest of the arguments are the names of the arguments to the
          -- constant.
          ← mkListLit typeIdType <| ← (params.zip paramInsts).toList.mapM fun (p, i) =>
              mkAppOptM ``typeId #[some p, some i],
        ]
      hints := .regular 10
      safety := .safe
    }
    -- Declare the axiom which states that the type id is correct.
    liftCoreM <| addDecl <| .axiomDecl {
      name := name ++ `typeId_ofType
      levelParams := levelParams
      type := ← liftTermElabM do
        -- Declare the parameters
        withLocalDeclsDND (paramNames.zip paramTypes) fun params => do
        -- Declare the instances
        withLocalDecls
          (params.map (fun p => (.anonymous, .instImplicit, fun _ => hasTypeIdType p)))
          fun paramInsts => do
        let paramInterleavedInsts :=
          (params.zip paramInsts |>.flatMap fun (a, b) => #[a, b])
        mkForallFVars paramInterleavedInsts <|
        ← mkAppM ``TypeId.OfType #[
          -- First argument is the type id
          ← mkAppM (name ++ `typeId) paramInterleavedInsts,
          -- Second is the type
          ← mkAppM name params,
        ]
      isUnsafe := false
    }
    -- Declare the instance of HasTypeId
    liftCoreM <| addDecl <| .defnDecl {
      name := name ++ `hasTypeId
      levelParams := levelParams
      type := ← liftTermElabM do sorry
      value := ← liftTermElabM do sorry
      hints := .regular 10
      safety := .safe
    }
    liftCoreM <| Attribute.add (name ++ `hasTypeId) `instance (← getRef)
    -- `(
    --   def $typeIdIdent $paramBinders* : TypeId where
    --     name := $nameTerm
    --     argIds := [$paramTypeIdTerms,*] -- TODO
    --   axiom $axiomIdent : TypeId.OfType ($typeIdIdent $paramIdents*) ($ident $paramIdents*)
    --   instance $instanceIdent:ident $paramBinders:bracketedBinder* : HasTypeId ($ident $paramIdents*) where
    --     typeId := $typeIdIdent
    --     h_correct := $axiomIdent
    -- )
  /-- Actually reads both the parameters and indices -/
  readParameters (x : InductiveVal) : CommandElabM (Array Expr × Expr) := do
    let mut params := #[]
    let mut t := x.type
    for _iParam in [0:x.numParams + x.numIndices] do
      match x.type.arrow? with
      | some (paramType, rest) => do
        params := params.push paramType
        t := rest
      | none => throwError m!"not enough parameters in type {x.name}"
    if not t.isSort then throwError m!"type {x.name} is not a sort"
    return (params, t)

initialize registerDerivingHandler ``HasTypeId derivingHandler
