module

public import Jrlean.Coc.Shadowed

namespace Jrlean.Coc.Var

@[expose]
public section

-- Local attributes
attribute [local grind] shadowedImpl Shadowed Unshadowed

-- de Bruijn
@[grind ., simp]
instance {n : Nat} : @Shadowed .deBruijn n.succ := by grind only [Shadowed.mk, shadowedImpl]
@[grind ., simp]
instance {n : Nat} [h_neZero : NeZero n] : @Shadowed .deBruijn n := by
  cases n
  case zero =>
    exfalso
    exact neZero_zero_iff_false.mp h_neZero
  case succ m =>
    infer_instance
@[grind ., simp]
instance : @Unshadowed .deBruijn 0 := by grind only [Unshadowed.mk, shadowedImpl]

-- Named
@[grind ., simp]
instance {n} {d : Nat} : @Shadowed .named ⟨n, d.succ⟩ := by grind only [Shadowed.mk, shadowedImpl]
@[grind ., simp]
instance {n} {d : Nat} [h_neZero : NeZero d] : @Shadowed .named ⟨n, d⟩ := by
  cases d
  case zero =>
    exfalso
    exact neZero_zero_iff_false.mp h_neZero
  case succ m =>
    infer_instance
@[grind ., simp]
instance {n} : @Unshadowed .named ⟨n, 0⟩ := by grind only [Unshadowed.mk, shadowedImpl]

variable {varKind : VarKind}
variable {x : Var'}

-- Opposite
@[grind _=_, simp]
theorem not_shadowed_iff_unshadowed : ¬x.Shadowed ↔ x.Unshadowed := by
  grind only [Unshadowed.mk]
@[grind _=_, simp]
theorem not_unshadowed_iff_shadowed : ¬x.Unshadowed ↔ x.Shadowed := by
  grind only [Unshadowed.mk]
@[simp]
theorem false_of_shadowed_of_unshadowed (h₁ : x.Shadowed) (h₂ : x.Unshadowed) : False := by
  grind only [Unshadowed.mk, Shadowed.mk]

-- Impl
theorem shadowed_iff_impl : x.Shadowed ↔ x.shadowedImpl := by
  grind only [Shadowed.mk, #b803, #4b51]
instance : Decidable x.shadowedImpl := by
  unfold shadowedImpl
  cases varKind <;> infer_instance

-- Decidablility
instance : Decidable x.Shadowed := decidable_of_iff' (@shadowedImpl varKind x) shadowed_iff_impl
instance : Decidable x.Unshadowed := by rw [←not_shadowed_iff_unshadowed]; infer_instance

-- Iff
@[grind =, simp]
theorem unshadowed_iff_eq_zero {x : @Var .deBruijn} : x.Unshadowed ↔ x = 0 := by
  apply Iff.intro
  · intro h
    cases x
    case zero => rfl
    case succ n =>
      exfalso
      grind only [=_ not_shadowed_iff_unshadowed, instShadowedOfNeZeroNat]
  · grind only [instUnshadowedOfNatVar']
@[grind _=_, simp]
theorem unshadowed_iff_depth_eq_zero {x : @Var .named} : x.Unshadowed ↔ x.depth = 0 := by
  obtain ⟨name, depth⟩ := x
  grind only [=_ not_shadowed_iff_unshadowed, Shadowed.mk, shadowedImpl, instUnshadowedMkOfNatNat,
    #3e7e]
@[grind =, simp]
theorem shadowed_iff_zero_lt {x : @Var .deBruijn} : x.Shadowed ↔ 0 < x.toNat := by
  grind only [= not_shadowed_iff_unshadowed, Shadowed.mk, = unshadowed_iff_eq_zero,
    instUnshadowedOfNatVar', shadowedImpl, =_ not_shadowed_iff_unshadowed, #0a85, #4b51]
@[grind =, simp]
theorem shadowed_iff_zero_lt_depth {x : @Var .named} : x.Shadowed ↔ 0 < x.depth := by
  grind only [= not_shadowed_iff_unshadowed, = unshadowed_iff_depth_eq_zero]
