module

import Init.Notation
public import Jrlean.Coc.Var

namespace Jrlean.Coc

public class Offset (varKind : VarKind) (α : Type) where
  offsetIn : α → Var' → α
  offsetOut : α → Var' → Option α

infix:arg "↑" => Offset.offsetIn
infix:arg "↓" => Offset.offsetOut

/--
info:
fun {varKind} [Offset varKind Var'] a b => (a↓b).get! : {varKind : VarKind} → [Offset varKind Var']
→ Var' → Var' → Var'
-/
#guard_msgs in
#check fun {varKind : VarKind} [Offset varKind Var'] (a b : Var') => Option.get! a↓b
