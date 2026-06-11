module

import Jrlean.HasTypeId.Basic

namespace Jrlean

/--
Types that implement `TypeName` are equal if and only if their names are
equal. This relies on some assumptions:
1. All types have unique names. These are namespace names, so this should be
   true for any two types in the same codebase.
2. All types that implement `TypeName` have no universe parameters and no type
   parameters.
-/
axiom eq_iff_typeName_eq α β [HasTypeId α] [HasTypeId β]
: α = β ↔ typeId α = typeId β

instance instDecidableEq α β [TypeName α] [TypeName β] : Decidable (α = β) :=
  decidable_of_iff (typeName α = typeName β) (eq_iff_typeName_eq α β).symm

#eval Nat = Int
#reduce typeName Nat

example : Dynamic := Dynamic.mk 0
example : typeName Nat = `Nat := by decide
