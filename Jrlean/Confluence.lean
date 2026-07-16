module

public import Jrlean.Relation
public import Jrlean.ReflexiveTransitiveClosure
public import Jrlean.Diamond
public import Init

namespace Jrlean

public section

/-!
A confluence property is a generalization of the `Diamond` property.
-/
class abbrev Confluence (r : Relation α α) := Diamond (r*)

namespace Confluence

variable {α : Sort u} {r : Relation α α}

theorem of_diamond : Diamond r → Confluence r := by
  intro instDiamond
  -- First we prove a smaller statement.
  have aux : ∀ a b c, (r*) a b → r a c → ∃ d, r b d ∧ (r*) c d := by
    intro a b c h_a_b h_a_c
    induction h_a_b using ReflTransClosure.rightInduction
    case refl a => grind
    case rightCons a b₁ b₂ h_a_b₁ h_b₁_b₂ ih =>
      -- We need to find the `d`, and it happens to be the one from the diamond property with the
      -- induction hypothesis's `d`.
      have ⟨d, h_b₁_d, h_c_d⟩ := ih h_a_c; clear ih h_a_c
      have ⟨e, h_b₂_e, h_d_e⟩ := Diamond.diamond b₁ b₂ d h_b₁_b₂ h_b₁_d
      have h_c_e : (r*) c e := h_c_d.rightCons h_d_e
      exact ⟨e, h_b₂_e, h_c_e⟩
  -- Now comes the main part
  suffices Diamond (r*) from .mk
  constructor; intro a b c h_a_b h_a_c
  -- In the lemma at the start, we did induction on `h_a_b`. Now we do on the other one.
  induction h_a_c using ReflTransClosure.rightInduction
  case refl a => exists b
  case rightCons a c₁ c₂ h_a_c₁ h_c₁_c₂ ih =>
    have ⟨d, h_b_d, h_c₁_d⟩ := ih assumption
    have ⟨e, h_d_e, h_c₂_e⟩ := aux c₁ d c₂ assumption assumption
    exact ⟨e, h_b_d.rightCons h_d_e, h_c₂_e⟩

instance [Diamond r] : Confluence r := .of_diamond inferInstance
