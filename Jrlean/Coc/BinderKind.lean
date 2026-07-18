module

namespace Jrlean.Coc

public inductive BinderKind where
  /-- λ -/
  | lam
  /-- Π -/
  | pi
  deriving DecidableEq, Inhabited, Hashable, Repr
