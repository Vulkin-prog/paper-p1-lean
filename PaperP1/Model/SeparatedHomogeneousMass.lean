module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Homogeneous mass on literally separated original complete windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedHomogeneousMass

open Finset PaperP1.Model PaperP1.HomogeneousRunMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Separated (L : ℕ) (T : Finset ℕ) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x + L ≤ y ∨ y + L ≤ x

def mass (L : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ T ∈ F.filter (Separated L), probability L T

theorem mono (L : ℕ) {F G : Finset (Finset ℕ)} (hFG : F ⊆ G) : mass L F ≤ mass L G := by
  apply sum_le_sum_of_subset_of_nonneg _ (fun T _ _ ↦ (probability_pos L T).le)
  intro T hT
  exact mem_filter.mpr ⟨hFG (mem_filter.mp hT).1, (mem_filter.mp hT).2⟩

theorem le_total (L : ℕ) (F : Finset (Finset ℕ)) : mass L F ≤ ∑ T ∈ F, probability L T :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun T _ _ ↦ (probability_pos L T).le)

theorem union_le (L : ℕ) (F G : Finset (Finset ℕ)) : mass L (F ∪ G) ≤ mass L F + mass L G := by
  unfold mass
  rw [filter_union]
  exact GraphStarWeights.sum_union_le_nonneg _ _ _ (fun T ↦ (probability_pos L T).le)

theorem biUnion_le {ι : Type*} [DecidableEq ι] (L : ℕ) (F : Finset ι)
    (A : ι → Finset (Finset ℕ)) : mass L (F.biUnion A) ≤ ∑ i ∈ F, mass L (A i) := by
  have heq : (F.biUnion A).filter (Separated L) = F.biUnion (fun i ↦ (A i).filter (Separated L)) := by
    ext T
    simp only [mem_filter, mem_biUnion]
    tauto
  unfold mass
  rw [heq]
  exact GraphStarWeights.sum_biUnion_le_nonneg F _ _ (fun T ↦ (probability_pos L T).le)

end PaperP1.SeparatedHomogeneousMass
