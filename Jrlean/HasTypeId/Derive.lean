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
  |>.mapM fun _ => mkFreshUserName suggestion

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
      command name params
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
  command (name : Name) (paramTypes : Array Expr) : CommandElabM Unit := do
    /-
    Does three things:
    1. declares a function called _.typeId
    2. declares an axiom _.typeId_ofType
    3. declares an instance of HasTypeId
    -/
    let paramNames ← liftCoreM <| generateNames paramTypes.size `a
    let paramTypeIdTerms ← paramNames.mapM (fun name =>
      `(HasTypeId.typeId $(mkIdent name))
    )
    -- An expression that returns the type `TypeId`
    let typeIdType : Expr := .const ``TypeId []
    -- Declare the type id
    liftCoreM <| addDecl (forceExpose := true) <| .defnDecl {
      name := name ++ `typeId
      levelParams := [] -- TODO
      type := ← liftCoreM <| mkArrowN paramTypes typeIdType -- TODO
      value := ← liftTermElabM do
        mkAppM ``TypeId.mk #[
          -- First argument is the constant's name
          toExpr name,
          -- The rest of the arguments are the names of the arguments to the
          -- constant.
          ← mkListLit typeIdType <| ← paramTypes.toList.mapM fun t =>
              mkAppM ``typeId #[t],
        ]
      hints := .regular 10
      safety := .safe
    }
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

initialize registerDerivingHandler ``TypeId derivingHandler
