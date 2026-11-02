module

public import Mathlib.Order.Partition.Finpartition
public import Lean.Elab.Tactic.Omega

/-! # A refinement without singleton parts cannot split two-element blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairFinpartition

open Finset

theorem eq_of_pair_refinement {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (P Q : Finpartition I) (hPQ : P ≤ Q)
    (hP : ∀ C ∈ P.parts, 2 ≤ C.card) (hQ : ∀ D ∈ Q.parts, D.card = 2) : P = Q := by
  apply le_antisymm hPQ
  intro D hD
  obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hD
  obtain ⟨C, hC, hxC⟩ := P.exists_mem (Q.le hD hx)
  obtain ⟨E, hE, hCE⟩ := hPQ hC
  have hED : E = D := Q.eq_of_mem_parts hE hD (hCE hxC) hx
  have hCD : C = D := eq_of_subset_of_card_le (hED ▸ hCE)
    (by rw [hQ D hD]; exact hP C hC)
  exact ⟨C, hC, by rw [hCD]⟩

end PaperP1.PairFinpartition
