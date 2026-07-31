module

public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.Sort
public import Jrlean.Coc.TermFreeVars

import Jrlean.Coc.VarOffsetingLemmas
import Jrlean.SetTactic

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

@[grind _=_, simp]
theorem Term.offsetOut_app_isSome
    : ((a b)↓v).isSome ↔ (a↓v).isSome ∧ (b↓v).isSome := by
  rw [offsetOut_app]
  set a' := a↓v
  set b' := b↓v
  cases a' <;> cases b'
  all_goals
    open Option in
    grind only [= isSome_bind, = bind_some, = isSome_some, = isSome_none, = any_some, =
    isSome_map, bind_none, bind_some, map_none, map_some, any_some, isSome_bind, isSome_map]

@[grind =, simp]
theorem Term.offsetOut_app_of_isSome
    (h : ((a b)↓v).isSome)
    : (a b)↓v = some ((a↓v).get! (b↓v).get!) := by
  rw [offsetOut_app]
  rw [offsetOut_app_isSome] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [Option.isSome_iff_exists] at h₁ h₂
  grind only [= Option.get!_some, = Option.bind_some, = Option.map_some, #3363, #8957]

@[grind _=_, simp] theorem Term.offsetIn_binder
    {k v v' ty body}
    : (binder k v' ty body)↑v = binder k v' (ty↑v) (body↑(v↑v')) := rfl
@[grind =, simp] theorem Term.offsetOut_binder
    {k v v' ty body}
    : (binder k v' ty body)↓v =
      (ty↓v).bind fun ty' => (body↓(v↑v')).map fun body' => binder k v' ty' body' := by
  conv => rhs; arg 2; intro ty'; rw [Option.map_eq_bind]
  rfl

@[grind =, simp]
theorem Term.offsetOut_binder_isSome
    {k v v' ty body}
    : ((binder k v' ty body)↓v).isSome ↔ (ty↓v).isSome ∧ (body↓(v↑v')).isSome := by
  rw [offsetOut_binder]
  set ty' := ty↓v
  set body' := body↓(v↑v')
  cases ty' <;> cases body'
  all_goals
    open Option in
    grind only [= isSome_bind, = bind_some, = isSome_some, = isSome_none, = any_some, =
    isSome_map, bind_none, bind_some, map_none, map_some, any_some, isSome_bind, isSome_map]

@[grind _=_, simp]
theorem Term.offsetOut_binder_of_isSome
    {k v v' ty body}
    (h : ((binder k v' ty body)↓v).isSome)
    : (binder k v' ty body)↓v = some (binder k v' (ty↓v).get! (body↓(v↑v')).get!) := by
  rw [offsetOut_binder]
  rw [offsetOut_binder_isSome] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [Option.isSome_iff_exists] at h₁ h₂
  obtain ⟨ty', h₁⟩ := h₁
  obtain ⟨body', h₂⟩ := h₂
  rw [h₁, h₂]
  simp only [Option.map_some, Option.bind_some, Option.get!_some]

@[grind =, grind →, simp]
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
        exact Var.offsetOut_offsetIn
    clear ih_ty ih_body h
    rw [Option.isSome_iff_exists] at h₁ h₂
    obtain ⟨ty',h₁⟩ := h₁
    obtain ⟨body',h₂⟩ := h₂
    grind only [= offsetOut_binder, = Option.bind_some, = Option.isSome_map, = Option.isSome_some]

