module

public import Jrlean.C.Typ
public import Jrlean.C.Expr

namespace Jrlean.C

/-- Check that an expression is well-typed under the given type. -/
def Expr.check : Typ → Expr → Bool
  | .int, .int _ => true
  | .int, .uOp _ e => check .int e
  | .int, .bOp _ e1 e2 => check .int e1 && check .int e2
  -- | _, _ => false
