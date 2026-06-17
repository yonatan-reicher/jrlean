module

public import Jrlean.HasTypeId

namespace Jrlean

public section

/--
The type of types that have a type id. This is useful because having a type id
allows us to decide equality on types and hash them.
-/
structure TypeWithId.{u} where mk' ::
  type : Type u
  instHasTypeId : HasTypeId type

namespace TypeWithId

abbrev mk t [HasTypeId t] : TypeWithId := ⟨t, inferInstance⟩

@[expose]
instance : CoeOut TypeWithId Type where
  coe t := t.1

instance : DecidableEq TypeWithId := by
  rintro ⟨t1, i1⟩ ⟨t2, i2⟩
  if h : t1 = t2 then
    apply Decidable.isTrue
    subst t2
    have : i1 = i2 := HasTypeId.all_eq i1 i2
    subst i2
    rfl
  else
    apply Decidable.isFalse
    grind only

@[expose]
instance {t : TypeWithId} : HasTypeId t := t.2

@[expose]
instance : Hashable TypeWithId where
  hash t := hash (typeId t)

instance : Repr TypeWithId where
  reprPrec t n := reprPrec (typeId t) n
