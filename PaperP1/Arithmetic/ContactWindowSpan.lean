module

public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Model.LocalRunRank

/-! # Two windows at exact contact span the full even class space of their union -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactWindowSpan

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets

local instance contactWindowSpanTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem value_union {x L : ℕ} (hx : 0 < x) : values x L ∪ values (x + L) L = values x (2 * L) := by
  rw [values_eq_interval hx, values_eq_interval (show 0 < x + L by omega), values_eq_interval hx]
  ext n
  simp only [mem_union, mem_Ico]
  omega

theorem shared_value {x L : ℕ} (hx : 0 < x) : x + L - 1 ∈ values x L ∩ values (x + L) L := by
  rw [values_eq_interval hx, values_eq_interval (show 0 < x + L by omega)]
  simp only [mem_inter, mem_Ico]
  omega

theorem joined_space {x L : ℕ} (hx : 0 < x) :
    squareClassSpace x L ⊔ squareClassSpace (x + L) L = squareClassSpace x (2 * L) := by
  have hshared := mem_inter.mp (shared_value (L := L) hx)
  calc
    _ = FiniteEvenSquareClasses.space (values x L) ⊔ FiniteEvenSquareClasses.space (values (x + L) L) := by
      rw [space_values, space_values]
    _ = FiniteEvenSquareClasses.space (values x L ∪ values (x + L) L) :=
      (FiniteEvenSquareClasses.space_union _ _ (x + L - 1) hshared.1 hshared.2).symm
    _ = _ := by rw [value_union hx, space_values]

theorem rank_add_local_relations {x L : ℕ} (hx : 0 < x) :
    Module.finrank F₂ (squareClassSpace x L ⊔ squareClassSpace (x + L) L : Submodule F₂ (ℕ →₀ F₂)) +
      Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (2 * L + 1)) = 2 * L := by
  rw [joined_space hx]
  exact LocalRunRank.squareClass_rank_add_relation_rank (L := 2 * L) hx

theorem relation_rank_le_defects {x B : ℕ} (hB : 1 ≤ B) :
    Module.finrank F₂ (WindowRelationCode.windowRelationCode x B) ≤
      (LocalRigidityCode.defectValues x B).card := by
  have h := WindowRelationCode.window_relation_finrank_le_defectCode x B hB
  have hd := Submodule.finrank_le (LocalRigidityCode.defectCode x B)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  exact h.trans hd

end PaperP1.ContactWindowSpan
