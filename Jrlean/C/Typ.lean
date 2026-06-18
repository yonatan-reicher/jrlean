module

namespace Jrlean.C

public section

/- A representation of a C type. Called `Typ` instead of `Type` because that is
   taken. -/
inductive Typ
  | int
  deriving DecidableEq

@[coe, expose, reducible]
def Typ.toType : Typ → Type
  | .int => Int32

instance Typ.instCoeSort : CoeSort Typ Type where coe := toType

@[simp, grind =]
theorem Typ.grind.coeSort : ∀ t : Typ, CoeSort.coe t = t.toType := by intro; rfl

instance Typ.instToString : ToString Typ where
  toString
    | .int => "int"

abbrev Value := (t : Typ) × t
