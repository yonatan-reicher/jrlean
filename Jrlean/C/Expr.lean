module

namespace Jrlean.C

public inductive UnaryOp
  | add
  | neg
  deriving DecidableEq

public inductive BinaryOp
  | add
  | sub
  | mul
  | div
  deriving DecidableEq

public inductive Expr
  | int : Int32 → Expr
  | uOp : UnaryOp → Expr → Expr
  | bOp : BinaryOp → Expr → Expr → Expr
