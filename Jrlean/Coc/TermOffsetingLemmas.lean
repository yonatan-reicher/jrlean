module

public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.Sort
public import Jrlean.Coc.TermFreeVars

import Jrlean.Coc.VarOffsetingLemmas

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
-- attribute [local simp low]
--   Offset.offsetIn
--   Offset.offsetOut

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

@[grind _=_, simp] theorem Term.offsetIn_binder
    {k v v' ty body}
    : (binder k v' ty body)↑v = binder k v' (ty↑v) (body↑(v↑v')) := rfl
@[grind =, simp] theorem Term.offsetOut_binder
    {k v v' ty body}
    : (binder k v' ty body)↓v =
      (ty↓v).bind fun ty' => (body↓(v↑v')).map fun body' => binder k v' ty' body' := by
  conv => rhs; arg 2; intro ty'; rw [Option.map_eq_bind]
  rfl

theorem Term.offsetOut_isSome_of
    (h : v ∉ t.freeVars)
    : (t↓v).isSome := by
  induction t generalizing v
  iterate 2 next => trivial -- prop | type
  case var v' =>
    replace h : v ≠ v' := by grind only [freeVars, = List.mem_cons]
    grind only [= offsetOut_var, usr Var.offsetOut_isSome_of_neq, = Option.isSome_map]
  case app t₁ t₂ ih₁ ih₂ =>
    simp only [offsetOut_app]
    simp only [freeVars, List.mem_append, not_or] at h
    specialize ih₁ h.left
    specialize ih₂ h.right
    rw [Option.isSome_iff_exists] at ih₁ ih₂
    grind only [= Option.isSome_bind, = Option.any_some, = Option.isSome_map, = Option.isSome_some,
      #7f84, #86b6]
  case binder k v' ty body ih_ty ih_body =>
    -- We want to apply the induction hypothesis on the type with the variable, but in the body, we
    -- want to apply with the variable offset in.
    have h₁ : (ty↓v).isSome := ih_ty <| by grind only [freeVars, = List.mem_append]
    have h₂ : (body↓(v↑v')).isSome := ih_body <| by
      clear h₁ ih_ty ih_body
      conv at h =>
        unfold freeVars
        rw [List.mem_append]
        rw [not_or]
        right
        rw [List.mem_filterMap]
        rw [not_exists]
        intro v''
        rw [Decidable.not_and_iff_not_or_not]
      replace h := h.right v↑v'
      cases h
      · assumption
      · exfalso
        rename (v↑v')↓v' ≠ some v => h
        apply h; clear h
        exact Var.offsetIn_offsetOut
    clear ih_ty ih_body h
    rw [Option.isSome_iff_exists] at h₁ h₂
    obtain ⟨ty',h₁⟩ := h₁
    obtain ⟨body',h₂⟩ := h₂
    grind only [= offsetOut_binder, = Option.bind_some, = Option.isSome_map, = Option.isSome_some]

