module

public import Jrlean.TypeId

namespace Jrlean

/- This module defines the type class and the axioms we are assuming. -/

/-- A relation whether a type id matches a type. -/
public opaque TypeId.OfType : TypeId → Sort u → Prop
/-- Each type has an id. -/
public axiom TypeId.exists_ofType t : ∃ id, OfType id t
/-- Each type's id is unique. -/
public axiom TypeId.eq_iff_typeId_eq {α β id1 id2}
(h1 : OfType id1 α) (h2 : OfType id2 β) : α = β ↔ id1 = id2

@[ext]
public class HasTypeId (α : Sort u) where
  typeId : TypeId
  h_correct : typeId.OfType α

export HasTypeId (typeId)

/-- Every type can have an instance of `HasTypeId` constructed for it. -/
public instance {α} : Nonempty (HasTypeId α) := by
  open Classical in
  let exists_id := TypeId.exists_ofType α
  let id := choose exists_id
  have : id.OfType α := by apply choose_spec exists_id
  exact Nonempty.intro ⟨id, this⟩
