module

import Jrlean.TypeId
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
axiom eq_iff_typeId_eq α β [HasTypeId α] [HasTypeId β]
: α = β ↔ typeId α = typeId β

instance {α β} [HasTypeId α] [HasTypeId β] : Decidable (α = β) :=
  decidable_of_iff (typeId α = typeId β) (eq_iff_typeId_eq α β).symm
