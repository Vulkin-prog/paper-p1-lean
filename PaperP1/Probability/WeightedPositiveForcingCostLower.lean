module

public import PaperP1.Probability.PositiveForcingCostLower

/-! # Selected directed pairs keep their exact heterogeneous positive weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPositiveForcingCostLower

open Finset PaperP1.Probability PaperP1.ForcingCoordinateCost
  PaperP1.PositiveForcingCostLower

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

theorem offsite_selected_sum (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (E : Finset (ι × ι)) (hE : E ⊆ directed G) :
    (∑ p ∈ E, weight P J F p) ≤ offsite G P J F := by
  rw [offsite_eq_pairs]
  exact sum_le_sum_of_subset_of_nonneg hE (fun p _ _ ↦ weight_nonneg P J F p)

theorem full_selected_sum (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true)
    (E : Finset (ι × ι)) (hE : E ⊆ directed G) :
    (∑ p ∈ E, weight P J F p) ≤ cost G P J F :=
  (offsite_selected_sum G P J F E hE).trans (offsite_le_full_cost G P J F hF)

end PaperP1.WeightedPositiveForcingCostLower
