module

public import Jrlean.HasTypeId.Basic
import Jrlean.TypeId
import Lean.Elab.Deriving
import Lean.PrettyPrinter

namespace Jrlean

/- In this module, we describe a thing called a derive handler. This
   will allow us to add `deriving TypeId` to types. -/

open Lean Elab Command

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
    | .inductInfo .. => pure ()
    | .axiomInfo ..
    | .defnInfo ..
    | .thmInfo ..
    | .opaqueInfo ..
    | .quotInfo ..
    | .ctorInfo ..
    | .recInfo .. =>
      throwError m!"cannot derive TypeId for constant '{name}' as it is not definition of a new unique type. ConstantInfo object: {constant_info}"
    command name
  return true
where
  getStx (name : Name) : CoreM Command :=
    let ident : Ident := mkIdent name
    let typeIdIdent := mkIdent (name ++ `typeId)
    let axiomIdent := mkIdent (name ++ `typeId_ofType)
    let nameExpr : Term := quote name
    let universeLevels := quote ([] : List Nat) -- TODO
    `(
      def $typeIdIdent : TypeId where
        name := $nameExpr
        universe_levels := $universeLevels
        arg_ids := [] -- TODO
      axiom $axiomIdent : TypeId.OfType $typeIdIdent $ident
      instance : HasTypeId $ident where
        typeId := $typeIdIdent
        h_correct := $axiomIdent
    )
  command (name : Name) : CommandElabM Unit := do
    elabCommand <| ← liftCoreM <| getStx name

initialize registerDerivingHandler ``TypeId derivingHandler
