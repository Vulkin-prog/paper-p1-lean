module

public import PaperP1.Algebra.FiniteSetValueSpan

/-! # Three local even spaces lose at most three anchor directions in their full union -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeFiniteValueSpan

open Finset PaperP1.FiniteSetValueSpan

variable {K V E : Type*} [DivisionRing K] [DecidableEq V] [AddCommGroup E] [Module K E]

theorem full_union_rank_le_three_even_add_three (f : V → E) (A B C : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    Module.finrank K (span (K := K) f ((A ∪ B) ∪ C)) ≤
      Module.finrank K ↥((evenSpace (K := K) f A ⊔ evenSpace (K := K) f B) ⊔ evenSpace (K := K) f C) + 3 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  let J := (evenSpace (K := K) f A ⊔ evenSpace (K := K) f B) ⊔ evenSpace (K := K) f C
  let T := span (K := K) f {a, b, c}
  have haT : span (K := K) f {a} ≤ T := span_mono f (by simp)
  have hbT : span (K := K) f {b} ≤ T := span_mono f (by simp)
  have hcT : span (K := K) f {c} ≤ T := span_mono f (by simp)
  have hcover : span (K := K) f ((A ∪ B) ∪ C) ≤ J ⊔ T := by
    rw [span_union, span_union]
    apply sup_le
    · apply sup_le
      · exact (span_le_even_sup_anchor f A a ha).trans
          (sup_le_sup (le_sup_of_le_left le_sup_left) haT)
      · exact (span_le_even_sup_anchor f B b hb).trans
          (sup_le_sup (le_sup_of_le_left le_sup_right) hbT)
    · exact (span_le_even_sup_anchor f C c hc).trans (sup_le_sup le_sup_right hcT)
  have hmono := Submodule.finrank_mono hcover
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq J T
  have hanc := rank_le_card (K := K) f ({a, b, c} : Finset V)
  have hcard₁ := card_insert_le a ({b, c} : Finset V)
  have hcard₂ := card_insert_le b ({c} : Finset V)
  rw [card_singleton] at hcard₂
  change Module.finrank K T ≤ ({a, b, c} : Finset V).card at hanc
  change Module.finrank K (span (K := K) f ((A ∪ B) ∪ C)) ≤ Module.finrank K J + 3
  omega

end PaperP1.ThreeFiniteValueSpan
