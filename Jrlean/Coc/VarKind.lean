module

namespace Jrlean.Coc

public section

/--
A C-style enum with only de Bruijn indices or named identifiers.

Defined as a class so that we may use type class inference to select the kind of variable
representation we want to use in a given context.
-/
@[grind]
class inductive VarKind where
  | deBruijn
  | named
  deriving DecidableEq, Inhabited, Hashable, Repr
