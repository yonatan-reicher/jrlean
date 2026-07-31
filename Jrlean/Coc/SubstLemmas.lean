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
import Jrlean.AndTactic

namespace Jrlean.Coc

public section

variable {varKind : VarKind}
variable {a b c : Term'}
variable {s : Term'} [IsSort s]
variable {x : Var}

attribute [local grind .]
  Var.subst
  Term.subst

@[grind =, simp]
theorem var_subst_eq
{x : Var'} {r}
: x.subst x r = r := by
  grind =>
    instantiate only [Var.subst]
    instantiate only [= Var.offsetOut_eq_none_of_eq]
    instantiate only [= Option.map_none]
    instantiate only [= Option.getD_none]

@[grind =, simp]
theorem var_subst_neq
{v : Var'}
(h_neq : v ≠ x)
: v.subst x r = (v↓x).get! := by
  grind =>
    instantiate only [Var.subst, usr Var.offsetOut_eq_some_of_neq]
    cases #f94d <;>
      instantiate only [= Option.map_some, = Option.get!_some] <;>
        instantiate only [= Option.getD_some]

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

attribute [local grind .] Option.isSome_iff_exists

@[grind =, simp]
theorem subst_of_not_mem_freeVars (h_not_mem : x ∉ a.freeVars) : a[x:=b] = (a↓x).get! := by
  induction a generalizing x
  iterate 2 next => simp only [subst_sort, Term.offsetOut_sort, Option.get!_some] -- prop | type
  case var v =>
    change x ∉ [v] at h_not_mem
    have : x ≠ v := by simpa using h_not_mem
    rw [subst_var_neq this.symm]
    rw [Term.offsetOut_var]
    grind only [usr Var.offsetOut_eq_some_of_neq, = Option.map_some, = Option.get_some,
      = Option.get!_some, #f94d]
  case app f arg ih_f ih_arg =>
    -- Deal with the assumption that x is not in the free variables of f of arg
    have ⟨h_mem_f, h_mem_arg⟩ : x ∉ f.freeVars ∧ x ∉ arg.freeVars := by simpa [Term.freeVars] using h_not_mem
    have ⟨h_isSome_f, h_isSome_arg⟩ : (f↓x).isSome ∧ (arg↓x).isSome := ⟨Term.offsetOut_isSome_of h_mem_f, Term.offsetOut_isSome_of h_mem_arg⟩
    -- rw [Option.eq_some_of_isSome this.2] at this
    -- repeat rw [Option.isSome_iff_exists] at this
    -- obtain ⟨⟨f', h_f⟩, ⟨arg', h_arg⟩⟩ := this
    -- Use the induction hypotheses
    unfold Term.subst
    rw [ih_f h_mem_f, ih_arg h_mem_arg]
    clear ih_f ih_arg
    clear h_mem_f h_mem_arg h_not_mem
    -- The actual proof
    rw [Term.offsetOut_app]
    grind only [Option.isSome_iff_exists, = Term.offsetOut.notation, = Term.offsetOut_app,
      = Term.offsetOut.eq_4, = Option.bind_apply, = Term.offsetOut.eq_1, = Option.bind_some,
      = Option.get!_some, = Term.offsetOut.eq_2, = Option.map_some, #17b2, #5740, #561f,
      #561f8aa956314c44, #6be5, #6be59dd89fba79d4, #574055ad259ec26a]
  case binder k y ty body ih_ty ih_body =>
    rw [Term.subst]
    rw [Term.offsetOut_binder]
    -- Setup some hard truths
    rw [Term.freeVars] at h_not_mem
    have : x ∉ ty.freeVars := by grind only [Term.freeVars, = List.mem_append]
    have : (body↓y).isSome := sorry
    have : x ∉ (body↓y).get!.freeVars := sorry
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
      grind only [→ eq_prop_or_type_of_isSort, = var_subst_neq]
  -- rest is candy
  all_goals
    cases s using isSort_cases
    all_goals contradiction

#reduce
  let t : @Term .deBruijn := Term.var 0 |>.app (Term.var 1) |>.app (Term.var 2)
  t[0 := Term.prop][0 := Term.type]

theorem double_subst
    (h_x_neq_y : x ≠ y)
    (h_not_mem : y ∉ a.freeVars)
    -- TODO: This is wrong. Need to figure this out on paper.
    -- First write down some examples, then figure out the general case.
    : t[y:=b][(x↓y).get!:=a] = t[x:=a↑(y↓x).get!][(y↓x).get!:=b[(x↓y).get!:=a]] := by
  induction t
  iterate 2 next => simp only [subst_sort] -- prop | sort
  case var z =>
    apply distinguish z x y h_x_neq_y <;> intro h₁ h₂ ; subst_vars
    case eq_y => grind only [Term.subst, = subst_var_eq, = var_subst_neq]
    case eq_x =>
      simp_all [Option.get_eq_get!]
      show a = (a↑(y↓z).get!)[(y↓z).get!:=b[(z↓y).get!:=a]]
      show a = (a↑(y↓z).get!)[(y↓z).get!:=b[(z↓y).get!:=a]]
      done

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
