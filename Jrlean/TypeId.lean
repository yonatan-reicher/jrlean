module

import Lean.LibrarySuggestions.Default

/-
This module defines the `HasTypeId` class. This class associates a unique
identifier to types, which can be used to check for type equality at runtime.

This is an extended version of the builtin `TypeName` class. Namely, it supports
all types, not just those that are without parameters and without universe
parameters.
-/

namespace Jrlean

/-- Represents the full evaluated name of a type, including it's universe levels
  and the full list of its type arguments. This only makes sense for types that
  are fully applied, and with "constant" arguments. -/
@[ext]
public structure TypeId where
  name : Lean.Name
  universe_levels : List Nat
  arg_ids : List TypeId
  deriving Repr, Inhabited, Hashable, TypeName

@[grind]
public def TypeId.size : TypeId → Nat
  | ⟨_, _, []⟩ => 1
  | ⟨n, u, h :: t⟩ => h.size + size ⟨n, u, t⟩

public def TypeId.inductionOnChildren
  {P : TypeId → Sort}
  (id : TypeId)
  (base : P { id with arg_ids := [] })
  (step : ∀ h t, P { id with arg_ids := t } → P { id with arg_ids := h :: t })
: P id := by
  rcases id with ⟨n, u, a⟩
  induction a
  case nil => exact base
  case cons h t ih =>
    apply step; simp
    apply ih; simp
    exact base
    exact step

@[grind .]
public theorem TypeId.size_gt_zero (id : TypeId) : id.size > 0 := by
  induction id using TypeId.inductionOnChildren <;> grind

grind_pattern TypeId.size_gt_zero => id.size

@[grind ., grind →]
public theorem TypeId.size_lt_of_mem_arg_ids (id1 id2 : TypeId)
: id2 ∈ id1.arg_ids → id2.size < id1.size := by
  intro h_mem
  rcases id1 with ⟨_, _, arg_ids⟩
  induction arg_ids
  case nil => contradiction
  case cons head tail ih =>
    rw [size]
    if h_eq : head = id2 then
      subst head
      grind
    else
      grind

@[induction_eliminator]
public def TypeId.induction
  {P : TypeId → Sort}
  (ind : ∀ id, (∀ arg ∈ id.arg_ids, P arg) → P id)
: ∀ id, P id := by
  /- rintro ⟨n, u, a⟩ -/
  /- let id : TypeId := ⟨n, u, a⟩ -/
  intro id
  induction h : id.size using Nat.strongRecOn generalizing id
  case ind n ih =>
    apply ind
    intro arg h_mem
    have : arg.size < n := by
      subst n
      exact size_lt_of_mem_arg_ids id arg h_mem
    exact ih arg.size this arg rfl

public def TypeId.beq (id1 id2 : TypeId) :=
  -- This is a property needed for proving termination
  let P id := id ∈ id1.arg_ids ∨ id ∈ id2.arg_ids
  id1.name == id2.name
  && id1.universe_levels == id2.universe_levels
  && List.isEqv
    (id1.arg_ids.attachWith P (by grind))
    (id2.arg_ids.attachWith P (by grind))
    (·.val.beq ·.val)
  termination_by max id1.size id2.size
  decreasing_by grind

public instance : BEq TypeId where
  beq := TypeId.beq

@[grind =, simp]
private theorem List.zip_eq {α} (l : List α)
: l.zip l = l.map fun x => (x, x) := by
  induction l
  case nil => rfl
  case cons h t ih => simpa using ih

@[simp]
private theorem List.isEqv_attachWith {α} P (l1 l2 : List α) {h1 h2} r
: List.isEqv (l1.attachWith P h1) (l2.attachWith P h2) (r ·.val ·.val)
= l1.isEqv l2 r := by
  repeat rw [List.isEqv_eq_decide]
  simp only [List.length_attachWith, List.getElem_attachWith]

instance : DecidableEq TypeId := by
  intro id1 id2
  -- the decidability is because of the equivalence to boolean equality
  suffices id1 = id2 ↔ id1 == id2 from decidable_of_iff' (id1 == id2) this
  -- break down the ids
  apply Iff.intro
  · intro h_eq
    subst id2
    -- proof by induction.
    induction id1
    case ind id ih =>
      -- deconstruct the id
      rcases id with ⟨n, u, a⟩
      change ∀ arg ∈ a, arg == arg at ih
      simp only [BEq.beq, TypeId.beq]
      suffices (a.attach.zip a.attach).all fun (l, r) => l == r by sorry
      -- now we just need to prove that all the children all equal
      suffices ∀ x ∈ a.attach.zip a.attach, x.1 == x.2 by sorry
      simp
      intros
      subst_vars
      apply ih
      assumption
  · intro h_beq
    ext1
    case name | universe_levels =>
      rw [BEq.beq] at h_beq
      unfold TypeId.beq at h_beq
      grind
    case arg_ids =>
      induction id1 <;> induction id2
      case ind.ind id1 id2 ih1 ih2 =>
        sorry

public class HasTypeId (α : Type) where
  typeId : List Lean.Name

-- Unfortunately, Lean does not implement this class for almost any type, so we
-- have to do it ourselves. What a shame.
deriving instance TypeName for Nat, Int, String, Bool

/--
Types that implement `TypeName` are equal if and only if their names are
equal. This relies on some assumptions:
1. All types have unique names. These are namespace names, so this should be
   true for any two types in the same codebase.
2. All types that implement `TypeName` have no universe parameters and no type
   parameters.
-/
axiom eq_iff_typeName_eq α β [TypeName α] [TypeName β]
: α = β ↔ typeName α = typeName β

instance instDecidableEq α β [TypeName α] [TypeName β] : Decidable (α = β) :=
  decidable_of_iff (typeName α = typeName β) (eq_iff_typeName_eq α β).symm

#eval Nat = Int
#reduce typeName Nat

example : Dynamic := Dynamic.mk 0
example : typeName Nat = `Nat := by decide
