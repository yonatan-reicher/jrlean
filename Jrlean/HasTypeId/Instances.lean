module

public import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic
meta import Jrlean.HasTypeId.Derive

namespace Jrlean

deriving instance TypeId for Nat, Int, String, Bool, PUnit


#print PUnit.typeId_ofType


abbrev P := ULift.{3, 1} Type = ULift.{3, 2} (Type 1)

def f (a : P) : Type → Type 1 := fun x => by
  let xNatLift : ULift.{3, 1} Type := ⟨x⟩
  let xCast := cast a xNatLift
  let xCastDown := xCast.down
  exact xCastDown

#print ULift
theorem badness (a : P) : False := by
  let x := f a Nat
  have h : x = f a Nat := rfl
  simp [f] at h
  rw [← eq_mp_eq_cast] at h
  simp at h

axiom a : P
#reduce f a Nat

