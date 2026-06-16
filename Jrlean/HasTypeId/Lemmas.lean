module

import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic

namespace Jrlean

/--
Types that implement `TypeName` are equal if and only if their names are
equal. This relies on some assumptions:
1. All types have unique names. These are namespace names, so this should be
   true for any two types in the same codebase.
2. All types that implement `TypeName` have no universe parameters and no type
   parameters.
-/
theorem eq_iff_typeId_eq {α β} [i1 : HasTypeId α] [i2 : HasTypeId β]
: α = β ↔ typeId α = typeId β := by
  apply Iff.intro
  · intro h_eq
    show i1.typeId = i2.typeId
    subst β
    rw [←TypeId.eq_iff_typeId_eq]
    · exact i1.h_correct
    · exact i2.h_correct
  · intro h_typeId_eq
    show α = β
    rw [TypeId.eq_iff_typeId_eq]
    · exact i1.h_correct
    · rw [h_typeId_eq]; exact i2.h_correct

@[grind →]
theorem eq_of_typeId_eq {α β} [HasTypeId α] [HasTypeId β]
(h_typeId_eq : typeId α = typeId β) : α = β := by
  grind [eq_iff_typeId_eq]

@[grind =]
theorem typeId_eq_of_eq {α} [i1 : HasTypeId α] [i2 : HasTypeId α]
 : @typeId α i1 = @typeId α i2 := by
  grind [eq_iff_typeId_eq]

/-- All instances are equal. -/
public theorem HasTypeId.unique {α : Sort u}
(inst1 inst2 : HasTypeId α) : inst1 = inst2 := by
  ext1
  grind

instance {α β} [HasTypeId α] [HasTypeId β] : Decidable (α = β) :=
  decidable_of_iff' (typeId α = typeId β) eq_iff_typeId_eq
