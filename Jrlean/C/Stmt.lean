module

public import Jrlean.C.Typ
public import Jrlean.C.Expr

namespace Jrlean.C

public inductive Stmt
  | expr : Expr → Stmt
  | varDecl (t : Typ) (name : String) (init : Option Expr)
