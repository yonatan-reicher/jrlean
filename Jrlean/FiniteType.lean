module

namespace Jrlean

class FiniteType (α : Type u) where
  elems : Array α
  complete : ∀ x, x ∈ elems := by decide

instance Fin.instFiniteType {n} : FiniteType (Fin n) where
  elems := Array.finRange n
  complete := by
    let elems := Array.finRange n
    have : elems.size = n := Array.size_finRange
    intro x
    suffices elems[x] = x by
      exact Array.mem_of_getElem this
    apply Array.getElem_finRange

instance Option.instFiniteType [FiniteType α] : FiniteType (Option α) where
  elems := #[none] ++ FiniteType.elems.map some
  complete := by
    intro x
    match x with
    | none => grind only [= Array.mem_append, = List.mem_toArray, = List.mem_cons]
    | some x =>
      suffices x ∈ FiniteType.elems by grind
      exact FiniteType.complete x

