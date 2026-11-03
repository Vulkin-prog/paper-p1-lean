module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod

/-! # A support in at least three distinct physical blocks contains a fixed source when two blocks are free -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoFreeBlockSupport

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem source_mem {s : ℕ} (color : V → Fin s ⊕ Fin 2) (F : Finset V)
    (hinj : Set.InjOn color (F : Set V)) (hcard : 3 ≤ F.card) :
    ∃ v ∈ F, ∃ i : Fin s, color v = Sum.inl i := by
  classical
  by_contra hnot
  have hfree : ∀ v ∈ F, ∃ t : Fin 2, color v = Sum.inr t := by
    intro v hv
    cases h : color v with
    | inl i => exact False.elim (hnot ⟨v, hv, i, h⟩)
    | inr t => exact ⟨t, rfl⟩
  have hsub : F.image color ⊆ (univ : Finset (Fin 2)).image (Sum.inr : Fin 2 → Fin s ⊕ Fin 2) := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hc
    obtain ⟨t, ht⟩ := hfree v hv
    exact mem_image.mpr ⟨t, mem_univ _, ht.symm⟩
  have hbound := (card_le_card hsub).trans card_image_le
  rw [card_image_of_injOn hinj, card_univ, Fintype.card_fin] at hbound
  omega

end PaperP1.TwoFreeBlockSupport
