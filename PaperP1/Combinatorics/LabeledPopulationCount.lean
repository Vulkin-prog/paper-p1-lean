module

public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Counting labeled pairs from the actual populations of their second coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LabeledPopulationCount

open Finset

theorem cardinal_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (α × β)) (A : ℝ)
    (hf : ∀ a : α, (((F.filter fun z ↦ z.1 = a).image Prod.snd).card : ℝ) ≤ A) :
    (F.card : ℝ) ≤ ((F.image Prod.fst).card : ℝ) * A := by
  let fibre (a : α) := F.filter fun z ↦ z.1 = a
  apply FiniteCoverCount.cardinal_le F (F.image Prod.fst) fibre A
  · intro z hz
    exact ⟨z.1, mem_image_of_mem _ hz, mem_filter.mpr ⟨hz, rfl⟩⟩
  · intro a _
    have hinj : Set.InjOn (fun z : α × β ↦ z.2) (fibre a) := by
      intro z hz w hw heq
      exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm) heq
    rw [← card_image_of_injOn hinj]
    exact hf a

end PaperP1.LabeledPopulationCount
