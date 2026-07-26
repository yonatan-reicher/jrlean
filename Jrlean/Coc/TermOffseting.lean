module

public import Jrlean.Coc.Term
public import Jrlean.Coc.Offseting
public import Jrlean.Coc.VarOffseting

import Jrlean.Of

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}

@[grind]
def Term.offsetIn (t : Term') (bound : Var') : Term' :=
  match t with
  | .prop => .prop
  | .type => .type
  | .var v => .var of v↑bound
  | .app f a => Term.app of f.offsetIn bound of a.offsetIn bound
  | .binder k v ty body => Term.binder k v of ty.offsetIn bound of body.offsetIn (bound↑v)

@[grind]
def Term.offsetOut (t : Term') (bound : Var') : Option Term' := do
  match t with
  | .prop => some .prop
  | .type => some .type
  | .var v => Term.var <| ← v↓bound
  | .app f a => (← f.offsetOut bound).app <| ← a.offsetOut bound
  | .binder k v ty body => Term.binder k v (← ty.offsetOut bound) (← body.offsetOut (bound↑v))

instance : Offset varKind Term' where
  offsetIn := Term.offsetIn
  offsetOut := Term.offsetOut

variable {t t' : Term'} {v v' : Var'}

@[grind _=_] theorem Term.offsetIn.notation : t↑v = t.offsetIn v := rfl
@[grind _=_] theorem Term.offsetOut.notation : t↓v = t.offsetOut v := rfl
