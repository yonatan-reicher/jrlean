module

public import Jrlean.TypeId

namespace Jrlean

/- This module defines the type class and the axioms we are assuming. -/

/-- A relation whether a type id matches a type. -/
public opaque TypeId.OfType : TypeId → Type → Prop
/-- Each type has an id. -/
public axiom TypeId.exists_ofType t : ∃ id, OfType id t
/-- Each type's id is unique. -/
public axiom TypeId.eq_of_ofType {t id1 id2}
: OfType id1 t → OfType id2 t → id1 = id2

@[ext]
public class HasTypeId (α : Type) where
  typeId : TypeId
  h_correct : typeId.OfType α

export HasTypeId (typeId)

/-- All instances are equal. -/
public theorem HasTypeId.unique (α : Type)
: ∀ (inst1 inst2 : HasTypeId α), inst1 = inst2 := by
  rintro ⟨id1, h1⟩ ⟨id2, h2⟩
  ext1
  show id1 = id2
  exact TypeId.eq_of_ofType h1 h2

/-- Every type can have an instance of `HasTypeId` constructed for it. -/
public instance {α} : Nonempty (HasTypeId α) := by
  open Classical in
  let exists_id := TypeId.exists_ofType α
  let id := choose exists_id
  have : id.OfType α := by apply choose_spec exists_id
  exact Nonempty.intro ⟨id, this⟩

