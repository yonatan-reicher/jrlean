module

public import Jrlean.Coc.Basic

namespace Jrlean.Coc.Term

public section

variable {varKind : VarKind}

@[grind, simp]
def moveIntoBinder (t : Term) (bound : Var) : Term :=
  match t with
  | type | prop => t
  | var v => var (v.moveIntoBinder bound)
  | app f a => app (f.moveIntoBinder bound) (a.moveIntoBinder bound)
  | binder k v ty body =>
    let ty := ty.moveIntoBinder bound
    let body := body.moveIntoBinder (bound.moveIntoBinder v.toVar)
    binder k v ty body

/-- Moves an entire term t out of it's binder. The second argument is a term to
  place instead of the latest bound variable. -/
@[grind, simp]
def moveOutOfBinder (t : Term) (bound : Var) (r : Term) : Term :=
  match t with
  | type | prop => t
  | var v => 
    match v.moveOutOfBinder bound with
    | none => r
    | some v => var v
  | app f a => app (f.moveOutOfBinder bound r) (a.moveOutOfBinder bound r)
  | binder k v ty body =>
    let ty := ty.moveOutOfBinder bound r
    let r := r.moveIntoBinder v.toVar
    let body := body.moveOutOfBinder (bound.moveIntoBinder v.toVar) r
    binder k v ty body

