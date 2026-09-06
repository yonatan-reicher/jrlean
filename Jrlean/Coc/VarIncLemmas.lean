module

public import Jrlean.Coc.Shadows
public import Jrlean.Coc.VarInc
--
-- import Jrlean.Coc.ShadowsLemmas
-- import Jrlean.Coc.ShadowedLemmas

namespace Jrlean.Coc.Var

@[expose]
public section

variable {varKind : VarKind}
variable {x y z : Var'}

attribute [local grind] inc shadows NamedVar

@[grind ., simp]
theorem inc_neq : x++ ≠ x := by grind only [inc, #aa1a]

@[grind =, simp]
theorem inc_inj : x++ = y++ ↔ x = y := by
  cases varKind
  · grind only [inc, #fa70]
  · apply Iff.intro
    · intro h
      change x.toNamedVar = y.toNamedVar
      rw [inc, inc] at h
      rw [NamedVar.ext_iff]
      grind only
    · grind only

@[grind ., simp]
theorem shadows_inc : x < x++ := by
  cases varKind
  · grind only [shadows, inc_neq, inc]
  · grind only [shadows, inc]

@[grind ., simp]
theorem shadowsEq_inc_iff_shadows : y++ ≤ x ↔ y < x := by
  cases varKind
  · grind only [shadows, inc, #a3bf]
  · apply Iff.intro
    · grind only [shadows, inc, #a6e5]
    · cases x <;> grind only [shadows, inc]

@[grind =, simp]
theorem shadows_inc_iff_shadowsEq : y < x++ ↔ y ≤ x := by
  by_cases h : x = y
  · subst y
    grind only [shadows_inc]
  · cases varKind
    · grind only [shadows, inc, #20d4]
    · obtain ⟨xName, xDepth⟩ := x
      obtain ⟨yName, yDepth⟩ := y
      grind only [shadows, inc]

@[grind =, simp]
theorem eq_inc {n} {d : Nat} : (⟨n, d.succ⟩ : @Var .named) = ((⟨n, d⟩ : @Var .named)++ : @Var .named) := rfl

@[grind =, simp]
theorem shadows_inc_inc : x++ < y++ ↔ x < y := by
  grind only [= shadows_inc_iff_shadowsEq, shadowsEq_inc_iff_shadows]
@[grind =, simp]
theorem shadowsEq_inc_inc : x++ ≤ y++ ↔ x ≤ y := by
  grind only [= shadows_inc_iff_shadowsEq, shadowsEq_inc_iff_shadows]
