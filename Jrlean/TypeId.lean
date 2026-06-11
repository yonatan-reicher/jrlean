module

/-
This module defines the `TypeId` type. This is just a runtime representation of
full names of types.
-/

namespace Jrlean

/-- Represents the full evaluated name of a type, including it's universe levels
  and the full list of its type arguments. This only makes sense for types that
  are fully applied, and with "constant" arguments. -/
@[ext]
public structure TypeId where
  name : Lean.Name
  -- TODO: rename these two fields
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

@[expose]
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
public theorem List.isEqv_attachWith {α} P (l1 l2 : List α) {h1 h2} r
: List.isEqv (l1.attachWith P h1) (l2.attachWith P h2) (r ·.val ·.val)
= l1.isEqv l2 r := by
  repeat rw [List.isEqv_eq_decide]
  simp only [List.length_attachWith, List.getElem_attachWith]

public instance : DecidableEq TypeId := by
  intro id1 id2
  -- the decidability is because of the equivalence to boolean equality
  suffices id1 = id2 ↔ id1.beq id2 from decidable_of_iff' (id1.beq id2) this
  -- break down the ids
  apply Iff.intro
  · intro h_eq
    subst id2
    -- proof by induction.
    induction id1
    case ind id ih =>
      -- deconstruct the id
      rcases id with ⟨n, u, a⟩
      change ∀ arg ∈ a, arg.beq arg at ih
      rw [TypeId.beq]
      change n == n && u == u && (a.attachWith _ _).isEqv (a.attachWith _ _) _
      suffices a.isEqv a TypeId.beq = true by simpa
      suffices ∀ (i : Nat) (h' : i < a.length), a[i].beq a[i] = true by
        simpa [List.isEqv_eq_decide]
      grind
  · intro h_beq
    induction id1 generalizing id2 with | _ id1 ih
    change ∀ arg ∈ id1.arg_ids, ∀ id, arg.beq id → arg = id at ih
    ext1
    case name | universe_levels =>
      rw [TypeId.beq] at h_beq
      grind
    case arg_ids =>
      -- Now all that's left is proving the lists of children are equal, knowing
      -- that the ids are bequal.
      have h_len_eq : id2.arg_ids.length = id1.arg_ids.length := by
        clear ih
        rw [TypeId.beq] at h_beq
        simp at h_beq
        replace h_beq : id1.arg_ids.isEqv id2.arg_ids TypeId.beq := by grind
        rw [List.isEqv_eq_decide] at h_beq
        split at h_beq
        · symm; assumption
        · contradiction
      ext1 i
      guard_target = id1.arg_ids[i]? = id2.arg_ids[i]?
      if h_i : i < id1.arg_ids.length then
        suffices id1.arg_ids[i] = id2.arg_ids[i] by grind
        apply ih id1.arg_ids[i] (List.getElem_mem h_i) id2.arg_ids[i]
        clear ih
        -- Now all that's left is to show these two are bequal!
        guard_target = (id1.arg_ids[i].beq id2.arg_ids[i]) = true
        rw [TypeId.beq] at h_beq; simp at h_beq
        replace h_beq : id1.arg_ids.isEqv id2.arg_ids TypeId.beq := by grind
        rw [List.isEqv_eq_decide] at h_beq
        grind
      else
        -- Both sides are none
        have : id1.arg_ids[i]? = none ∧ id2.arg_ids[i]? = none := by
          grind only [List.getElem?_eq_none]
        rw [this.1, this.2]
