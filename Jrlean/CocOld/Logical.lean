module

public import Jrlean.Coc.Basic
public import Jrlean.Coc.Repr
public import Jrlean.Of

namespace Jrlean.Coc.Term

public section

variable {varKind : VarKind}

@[expose]
def implies : Term :=
  -- We are making λx. λy. x -> y. x and y are propositions, and we also have an anonymous variable
  -- for the proof of x.
  let x : Var := default
  let y : Var := default
  let xProof : Var := VarDecl.anonymous.toVar
  lam x.toDecl prop <| lam y.toDecl prop
  <| pi xProof.toDecl (var <| x.moveIntoBinder y)
  <| var (y.moveIntoBinder xProof)

def implies' : Term → Term → Term
  | x, y => implies.app x |>.app y

local infixr:50 " => " => implies'

@[expose]
def false : Term :=
  -- Π x : Prop . x
  let x : Var := default
  pi x.toDecl prop of var x

@[expose]
def true : Term :=
  -- Π x : Prop . x -> x
  let x : Var := default
  pi x.toDecl prop of var x => var x

@[expose]
def not : Term :=
  -- λ x : Prop . x -> False
  let x : Var := default
  lam x.toDecl prop of var x => false

@[expose]
def and : Term :=
  -- λ x : Prop . λ y : Prop . Π z : Prop . (x -> y -> z) -> z
  let x : Var := default
  let y : Var := default
  let z : Var := default
  lam x.toDecl prop <| lam y.toDecl prop
  <| pi z.toDecl prop
  <| let x := x.moveIntoBinder y |>.moveIntoBinder z
     let y := y.moveIntoBinder z
     (var x => var y => var z) => var z

@[expose]
def bool :=
  -- Π x : Prop . x -> x -> x
  let x : Var := default
  pi x.toDecl prop of var x => var x => var x

-- #eval @implies .named
-- #eval let : VarKind := .named; app not false |>.betaReduce
