module

public import Jrlean.Coc.Subst
public import Jrlean.Coc.Sort
public import Jrlean.Coc.VarOffseting
public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermFreeVars

import Jrlean.Coc.VarOffsetingLemmas
import Jrlean.Coc.TermOffsetingLemmas

import Jrlean.Assumption
import Jrlean.ByContra
import Jrlean.SetTactic

namespace Jrlean.Coc

public section

variable {varKind : VarKind}
variable {a b c : Term'}
variable {s : Term'} [IsSort s]
variable {x : Var}

@[grind =, simp]
theorem var_subst_eq
{x : Var'} {r}
: x.subst x r = r := by
  simp only [Var.subst, Var.offsetOut.simp_notation, Var.offsetOut]
  grind only [= Var.offsetOutDeBruijn.eq_1, = Option.map_none, = Option.getD_none,
    = Var.offsetOutNamed.eq_1, #f010]

@[grind =, simp]
theorem var_subst_neq
{v : Var'}
(h_neq : v ≠ x)
: v.subst x r = (v↓x).get! := by
  -- By the definition of subst, we just need to show it's not none
  show (v↓x |>.map var |>.getD r) = (v↓x).get!
  suffices v↓x ≠ none by
    have : ∃ v', v↓x = some v' := Option.ne_none_iff_exists'.mp this
    grind only [= id.eq_1, = Option.get!_some, = Option.map_some, = Option.getD_some, #4c12]
  -- We need to treat each case differently sadly
  cases varKind
  · simp only [Var.offsetOut.simp_notation, Var.offsetOut, Var.offsetOutDeBruijn, Var.toNat,
    gt_iff_lt, ne_eq, ite_eq_left_iff, not_imp]
    grind only
  · simp [Var.offsetOutNamed]
    if h_name : v.name = x.name then
      have h_depth: v.depth ≠ x.depth := by grind only [NamedVar.ext]
      simp [h_name, h_depth]
      grind only [→ eq_prop_or_type_of_isSort, = Option.map_some, = Option.getD_some, #baf6]
    else
      simp [h_name]

@[grind =, simp]
theorem subst_var_eq : x[x:=a] = a := by simp [Term.subst]

@[grind =, simp]
theorem subst_var_neq (h : x ≠ y)
    : x[y:=a] = (x↓y).get (by exact Var.offsetOut_isSome_of_neq h) := by
  grind only [Term.subst, = var_subst_neq, usr Var.offsetOut_eq_some_of_neq, = Option.get!_some,
    = Option.get_some, #4d66]

@[grind =, simp]
theorem subst_sort : s[x:=a] = s := by
  cases s using isSort_cases
  all_goals rfl

@[grind =, simp]
theorem subst_of_not_mem_freeVars (h_not_mem : x ∉ a.freeVars) : a[x:=b] = (a↓x).get! := by
  induction a
  iterate 2 next => simp only [subst_sort, Term.offsetOut_sort, Option.get!_some] -- prop | type
  case var v =>
    change x ∉ [v] at h_not_mem
    have : x ≠ v := by simpa using h_not_mem
    rw [subst_var_neq this.symm]
    rw [Term.offsetOut_var]
    grind only [usr Var.offsetOut_eq_some_of_neq, = Option.map_some, = Option.get_some,
      = Option.get!_some, #f94d]
  case app f arg ih_f ih_arg =>
    unfold Term.subst
    rw [ih_f, ih_arg]
    simp only [Term.offsetOut_app]
    grind
    sorry

theorem subst_eq_sort [IsSort s]
(h : a[x:=b] = s)
: a = s ∨ (a = x ∧ b = s) := by
  cases a <;> unfold Term.subst at h
  -- prop | type
  iterate 2 exact .inl assumption
  -- main case
  case var v =>
    if h_v : v = x then
      -- Replaced! that means b was it
      right; show var v = x ∧ b = s
      grind only [= var_subst_eq, = id.eq_1]
    else
      -- Not replaced! that means it was already s
      left; show v = s
      simp only [ne_eq, h_v, not_false_eq_true, var_subst_neq, Var.offsetOut.simp_notation] at h
      grind only [→ eq_prop_or_type_of_isSort]
  -- rest is candy
  all_goals
    cases s using isSort_cases
    all_goals contradiction

theorem double_subst
    (h_x_neq_y : x ≠ y)
    (h_not_mem : y ∉ a.freeVars)
    : t[y:=b][(x↓y).get!:=a] = t[x:=a][y:=b[x:=a]] := by
  induction t
  iterate 2 next => simp only [subst_sort] -- prop | sort
  case var z =>
    apply distinguish z x y h_x_neq_y <;> intro h₁ h₂ ; subst_vars
    case eq_x =>
      simp [h_x_neq_y]
      simp_all
      rw [subst_var_neq, subst_var_eq]
      simp

    case x =>
    · subst y z
      simp
    if h_x : z = x then
      subst z
      simp
      if h_y : x = y then
        subst y
        simp
      else
        done
      simp
      
    else
      done
  all_goals grind [Term.subst]
  case app f arg ih_f ih_arg => grind [Term.subst]
where
  distinguish {α} [DecidableEq α]
      (z x y : α) (h_x_neq_y : x ≠ y)
      {motive : Prop}
      (eq_x : z = x → z ≠ y → motive)
      (eq_y : z = y → z ≠ x → motive)
      (neither  : z ≠ x → z ≠ y → motive)
      : motive := by
    by_cases h₁ : z = x <;> by_cases h₂ : z = y
    all_goals grind only
