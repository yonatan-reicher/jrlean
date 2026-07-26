module

public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.Sort

namespace Jrlean.Coc

@[expose]
public section

variable {varKind : VarKind}
variable {v v' : Var'}
variable {t t' a b c : Term'}
variable {s s' : Term'} [IsSort s] [IsSort s']

attribute [local grind .]
  Offset.offsetIn
  Offset.offsetOut
  instOffsetTerm'
  Term.offsetIn
  Term.offsetOut
attribute [local simp]
  Offset.offsetIn
  Offset.offsetOut

@[grind =, simp] theorem Term.offsetIn_sort : s↑v = s := by grind
@[grind =, simp] theorem Term.offsetOut_sort : s↓v = s := by grind
@[grind =, simp] theorem Term.offsetIn_var : (var v)↑v' = var (v↑v') := rfl
@[grind =, simp] theorem Term.offsetOut_var : (var v)↓v' = (v↓v').map var := by
  by_cases h : v↓v' = none
  · grind
  · have : ∃ a, v↓v' = some a := Option.ne_none_iff_exists'.mp h
    grind

@[grind _=_, simp] theorem Term.offsetIn_app : (a b)↑v = (a↑v) (b↑v) := rfl
@[grind =, simp] theorem Term.offsetOut_app
    : (a b)↓v = (a↓v).bind fun a => (b↓v).map fun b => a b := by
  simp only [Offset.offsetOut]
  rw [Term.offsetOut]
  change (offsetOut a v |>.bind fun a => offsetOut b v |>.bind fun b => some (a b)) = _
  conv => rhs; rhs; intro a; rw [Option.map_eq_bind]
  rfl
