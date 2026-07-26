module

public import Jrlean.Coc.Term

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}

@[grind, simp]
def Term.isSort : Term' → Bool
  | prop | type => true
  | _ => false

def Term.Sort := { t : Term' // t.isSort }
def Term.Sort' [varKind : VarKind] := @Term.Sort varKind

@[grind]
class IsSort (a : Term') where isSort : a.isSort
instance : IsSort (@Term.prop varKind) where isSort := rfl
instance : IsSort (@Term.type varKind) where isSort := rfl

@[grind →, simp]
theorem eq_prop_or_type_of_isSort
    (s : Term') [IsSort s]
    : s = .prop ∨ s = .type := by grind

@[elab_as_elim]
theorem isSort_cases
    (s : Term')
    [IsSort s]
    {motive : Term' → Prop}
    (prop : motive .prop)
    (type : motive .type)
    : motive s := by
  cases eq_prop_or_type_of_isSort s <;> {
    subst s
    assumption
  }
