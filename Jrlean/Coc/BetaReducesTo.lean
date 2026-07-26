module

public import Jrlean.Coc.Term
public import Jrlean.Coc.Subst

import Jrlean.Coc.TermNotation
import Jrlean.Coc.VarConversions
import Jrlean.SetTactic

public import Jrlean.Relation

namespace Jrlean.Coc

variable {varKind : VarKind}

@[grind]
public inductive Term.BetaReducesTo : Relation Term' Term' where
  /-- A redex is a term that has a head as written here, and hence is reducible. -/
  | redex {x a ty body} : ((λ x : ty . body) a).BetaReducesTo body[x:=a]
  | reduceFunc {f g a : Term} : f.BetaReducesTo g → (f a).BetaReducesTo (g a)
  | reduceArg {a b f : Term} : a.BetaReducesTo b → (f a).BetaReducesTo (f b)
  | reduceBinderType {k x ty ty' body}
    : ty.BetaReducesTo ty' → (binder k x ty body).BetaReducesTo (binder k x ty' body)
  | reduceBinderBody {k x ty body body'}
    : body.BetaReducesTo body' → (binder k x ty body).BetaReducesTo (binder k x ty body')

-- Terms
variable {a b c d e f g : Term}
variable {t t' : Term}
variable {ty ty' body body' : Term}
-- Variables
variable {x y z : VarDecl}
-- Binder kind
variable {k k' : BinderKind}


theorem Term.betaReducesTo_prop
(h_prop : t.BetaReducesTo prop)
: (∃ x ty a, t = (λ x : ty . prop) a) ∨ (∃ x ty, t = (λ x : ty . x) prop) := by
  -- Call the rhs t' so we can use elimination
  set t' := prop with h_t'
  cases h_prop
  -- Redex!
  case redex x a ty body =>
    sorry

