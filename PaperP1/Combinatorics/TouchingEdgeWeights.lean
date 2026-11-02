module

public import PaperP1.Combinatorics.SharedPairProducts

/-! # Edge weights meeting a marked set are bounded by the marked row sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TouchingEdgeWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

def touching (G F : Finset ι) : Finset (Finset ι) := by
  classical
  exact (G.powersetCard 2).filter (fun e ↦ ∃ x ∈ F, x ∈ e)

theorem cover (G F : Finset ι) :
    touching G F ⊆ F.biUnion (SharedPairProducts.incident G) := by
  classical
  intro e he
  obtain ⟨he, x, hxF, hxe⟩ := mem_filter.mp he
  exact mem_biUnion.mpr ⟨x, hxF, mem_filter.mpr ⟨he, hxe⟩⟩

theorem sum_bound (G F : Finset ι) (hFG : F ⊆ G) (w : Finset ι → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ e ∈ touching G F, w e) ≤ ∑ x ∈ F, ∑ y ∈ G.erase x, w {x, y} := by
  classical
  calc
    _ ≤ ∑ e ∈ F.biUnion (SharedPairProducts.incident G), w e :=
      sum_le_sum_of_subset_of_nonneg (cover G F) (fun e _ _ ↦ hw e)
    _ ≤ ∑ x ∈ F, ∑ e ∈ SharedPairProducts.incident G x, w e :=
      GraphStarWeights.sum_biUnion_le_nonneg F (SharedPairProducts.incident G) w hw
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      exact SharedPairProducts.incident_sum G x (hFG hx) w

end PaperP1.TouchingEdgeWeights
