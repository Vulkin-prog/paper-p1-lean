module

public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

/-! # Inclusion-exclusion for three finite sets without natural-number subtraction -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ThreeUnionCard

open Finset

theorem identity {V : Type*} [DecidableEq V] (A B C : Finset V) :
    ((A ∪ B) ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card =
      A.card + B.card + C.card + ((A ∩ B) ∩ C).card := by
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) C
  rw [union_inter_distrib_right] at h₂
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have heq : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by
    ext n
    simp only [mem_inter]
    constructor
    · rintro ⟨⟨ha, hc⟩, hb, _hc'⟩
      exact ⟨⟨ha, hb⟩, hc⟩
    · rintro ⟨⟨ha, hb⟩, hc⟩
      exact ⟨⟨ha, hc⟩, hb, hc⟩
  rw [heq] at h₃
  omega

end PaperP1.ThreeUnionCard
