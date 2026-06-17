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
  -- |>.mapM fun i => mkFreshUserName (suggestion.appendAfter <| toString i)
  |>.mapM fun i => return suggestion.appendAfter <| toString i

def _root_.Array.interleave? {α} (xs ys : Array α) :=
  if xs.size != ys.size then none
  else some <| xs.zip ys |>.flatMap fun (x, y) => #[x, y]

def _root_.Array.interleave! {α} (xs ys : Array α) :=
  match Array.interleave? xs ys with
  | some zs => zs
  | none => panic! s!"arrays have different sizes: {xs.size} != {ys.size}"

def _root_.Lean.Level.containsLevelParam (l : Name) : Level → Bool
  | .param l' => l == l'
  | .succ l' => containsLevelParam l l'
  | .max l1 l2 => containsLevelParam l l1 || containsLevelParam l l2
  | .imax l1 l2 => containsLevelParam l l1 || containsLevelParam l l2
  | _ => false

def _root_.Lean.Expr.containsLevelParam (l : Name) : Expr → Bool
  | .sort l' => l'.containsLevelParam l
  | .app f a => f.containsLevelParam l || a.containsLevelParam l
  | .lam _name binderType body _binderInfo
  | .forallE _ binderType body _ =>
    binderType.containsLevelParam l || body.containsLevelParam l
  | .letE _ type value body _ =>
    type.containsLevelParam l
    || value.containsLevelParam l
    || body.containsLevelParam l
  | .proj _ _ e => e.containsLevelParam l
  | .mdata _ e => e.containsLevelParam l
  | .lit _ => false
  | .const _ ls => ls.any (·.containsLevelParam l)
  | .mvar _
  | .fvar _
  | .bvar _ => false


/--
A deriving handler is a function that takes an array of names, and for each name,
declares something for it. In our case, this will define an implementation of
the `HasTypeId` type class.
-/
def derivingHandler : DerivingHandler := fun names => do
  names.forM deriveForName
  return true
where
  deriveForName (name : Name) : CommandElabM Unit := do
    let inductiveVal ← getInductiveVal! name
    deriveForInductive inductiveVal
  getInductiveVal! name := do
    let constantInfo ← getConstInfo name
    match constantInfo with
    | .inductInfo inductiveVal => return inductiveVal
    | .axiomInfo ..
    | .defnInfo ..
    | .thmInfo ..
    | .opaqueInfo ..
    | .quotInfo ..
    | .ctorInfo ..
    | .recInfo .. =>
      throwError m!"cannot derive TypeId for constant '{name}' as it is not definition of a new unique type. ConstantInfo object: {constantInfo}"
  deriveForInductive (ind : InductiveVal) := do
    -- In Lean, inductives can have both parameters and indices. For our
    -- purposes, these are the same, so we'll just refer to all of them as
    -- parameters.
    let (paramTypes, _retType) ← readParameters ind
    let paramNames ← liftCoreM <| generateNames paramTypes.size `a
    let paramNamesWithTypes := paramNames.zip paramTypes
    let levelParams := ind.levelParams.filter (fun l =>
      paramTypes.any (·.containsLevelParam l))
    declareTypeId ind paramNamesWithTypes levelParams
    declareAxiom ind paramNamesWithTypes
    declareInstance ind paramNamesWithTypes
    liftCoreM <| compileDecls #[
      ind.name ++ `typeId,
      ind.name ++ `typeId_ofType,
      ind.name ++ `instHasTypeId
    ]
  withParamFVars (params : Array (Name × Expr)) k := do
    -- Declare the parameters
    withLocalDeclsDND params fun paramFVars => do
    -- Declare the instances
    let insts := (params.zip paramFVars).map fun (p, v) => (
      p.1.appendBefore "inst",
      BinderInfo.instImplicit,
      fun _ => hasTypeIdType v,
    )
    withLocalDecls insts fun instsFVars => do
    k paramFVars instsFVars
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
  -- TODO: rename this levelParams parameter (and in the rest of the code too)
  declareTypeId ind params levelParams := do
    -- Declare the type id
    liftCoreM <| addDecl (forceExpose := true) <| .defnDecl {
      name := ind.name ++ `typeId
      levelParams := levelParams
      type := ← liftTermElabM do
        withParamFVars params fun paramFVars instsFVars => do
          mkForallFVars (paramFVars.interleave! instsFVars) typeIdType
      value := ← liftTermElabM do
        withParamFVars params fun paramFVars instsFVars => do
          mkLambdaFVars
            (paramFVars.interleave! instsFVars)
            <| ← mkAppM ``TypeId.mk #[
              -- First argument is the constant's name
              toExpr ind.name,
              -- The rest of the arguments are the names of the arguments to the
              -- constant.
              ← mkListLit typeIdType <|
              ← (paramFVars.zip instsFVars).toList.mapM fun (p, i) =>
                  mkAppOptM ``typeId #[some p, some i],
            ]
      hints := .regular 10
      safety := .safe
    }
  declareAxiom ind params := do
    liftCoreM <| addDecl <| .axiomDecl {
      name := ind.name ++ `typeId_ofType
      levelParams := ind.levelParams
      type := ← liftTermElabM do
        withParamFVars params fun paramFVars instsFVars => do
          mkForallFVars (paramFVars.interleave! instsFVars) <|
          ← mkAppM ``TypeId.OfType #[
            -- First argument is the type id
            ← typeId ind.name paramFVars instsFVars,
            -- Second is the type
            mkAppN (.const ind.name <| ind.levelParams.map .param) paramFVars,
          ]
      isUnsafe := false
    }
  declareInstance ind params := do
    liftCoreM <| addDecl (forceExpose := true) <| .defnDecl {
      name := ind.name ++ `instHasTypeId
      levelParams := ind.levelParams
      type := ← liftTermElabM do
        withParamFVars params fun paramFVars instsFVars => do
          mkForallFVars (paramFVars.interleave! instsFVars) <|
          ← hasTypeIdType (mkAppN (.const ind.name (ind.levelParams.map .param)) paramFVars)
      value := ← liftTermElabM do
        withParamFVars params fun paramFVars instsFVars => do
          mkLambdaFVars (paramFVars.interleave! instsFVars) <|
            ← mkAppM ``HasTypeId.mk #[
              -- First argument is the type id
              ← typeId ind.name paramFVars instsFVars,
              -- Second is the proof - which is just the axiom we declared above.
              ← mkAppOptM'
                (.const (ind.name ++ `typeId_ofType) (ind.levelParams.map .param))
                (paramFVars.interleave! instsFVars |>.map some)
            ]
      hints := .regular 10
      safety := .safe
    }
    let ident := mkCIdent (ind.name ++ `instHasTypeId)
    -- I couldn't figure out how to use Lean.Attribute.add so I just used
    -- `elabCommand` instead.
    elabCommand <| ← `(attribute [reducible, instance] $ident)
  typeIdType : Expr := .const ``TypeId []
  hasTypeIdType (α : Expr) := mkAppM ``HasTypeId #[α]
  typeId name paramFVars instsFVars :=
    mkAppOptM (name ++ `typeId) (paramFVars.interleave! instsFVars |>.map some)

initialize registerDerivingHandler ``HasTypeId derivingHandler
