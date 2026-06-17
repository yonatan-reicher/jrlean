module

public import Std

namespace Jrlean

open Std (ExtHashSet)

public section

/-
Init already has a class called `LawfulSingleton`, but that's about it.
-/

class LawfulEmptyCollection (α C) [EmptyCollection C] [Membership α C] where
  not_mem_empty : ∀ x : α, x ∉ (∅ : C)

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
: LawfulEmptyCollection α (ExtHashSet α) where
  not_mem_empty x := by grind

namespace LawfulEmptyCollection

attribute [grind ., simp] not_mem_empty

end LawfulEmptyCollection


class LawfulInsert (α C) [Insert α C] [Membership α C] [BEq α] where
  mem_insert_iff (x y : α) (s : C) : y ∈ insert x s ↔ x == y ∨ y ∈ s

instance {α} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
: LawfulInsert α (ExtHashSet α) where
  mem_insert_iff x y s := by
    simp only [ExtHashSet.insert_eq_insert, ExtHashSet.mem_insert]

namespace LawfulInsert

attribute [grind =, simp] mem_insert_iff

attribute [grind =, grind =_] insert_empty_eq

@[grind ., simp]
theorem mem_singleton_self {α C} (x : α)
[BEq α] [EquivBEq α]
[EmptyCollection C] [Insert α C] [Membership α C] [Singleton α C]
[LawfulInsert α C] [LawfulSingleton α C]
: x ∈ (singleton x : C) := by
  grind only [=_ insert_empty_eq, = mem_insert_iff]

@[grind =, simp]
theorem mem_singleton_iff {α C} (x y : α)
[BEq α] [EquivBEq α]
[EmptyCollection C] [Insert α C] [Membership α C] [Singleton α C]
[LawfulEmptyCollection α C] [LawfulInsert α C] [LawfulSingleton α C]
: x ∈ (singleton y : C) ↔ y == x := by
  grind only [=_ insert_empty_eq, = mem_insert_iff,
  LawfulEmptyCollection.not_mem_empty, #ccfa]

end LawfulInsert

-- Why isn't this in the standard library?
instance {α} [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
: LawfulSingleton α (ExtHashSet α) where
  insert_empty_eq x := by
    simp only [ExtHashSet.insert_eq_insert, ExtHashSet.singleton_eq_insert]
