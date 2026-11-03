module

public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Coding.MaximalSupportWord

/-! # Effective projection rank produces an actual heavy even physical relation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeavyPhysicalRelations

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

local instance heavyPhysicalPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι : Type*} [Fintype ι]

theorem exists_relation (X : ι → ℕ) (L : ℕ) (hX : ∀ j, 0 < X j) (a : ι)
    (t : ℕ) (ht : Even t)
    (hdim : t - 1 ≤ Module.finrank F₂ (LinearMap.range (effectiveProjection X L a))) :
    ∃ w : ι → Fin (L + 1) → F₂, (∀ j, (∑ i, w j i) = 0) ∧
      t ≤ (PaperP1.BinaryEvenSelections.selected (w a)).card ∧
      (∑ j, ∑ i, w j i • parityVec (X j - 1 + i.val)) = 0 := by
  have heven (v : LinearMap.range (projection X L a)) : (∑ i, v.val i) = 0 := by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw]
    change (∑ i, w.val (a, i)) = 0
    simpa only [startVertexSum_apply] using w.property.1 a
  obtain ⟨v, hv⟩ := PaperP1.MaximalSupportWord.exists_even_large_word
    (LinearMap.range (projection X L a)) heven t ht
    (hdim.trans (effective_projection_rank_le X L a))
  obtain ⟨w, hw⟩ := v.property
  refine ⟨fun j i ↦ w.val (j, i), ?_, ?_, ?_⟩
  · intro j
    simpa only [startVertexSum_apply] using w.property.1 j
  · rw [← hw] at hv
    exact hv
  · calc
      _ = ∑ j, vertexParityMap (X j) L (fun i ↦ w.val (j, i)) := by
        apply sum_congr rfl
        intro j _
        rw [vertexParityMap_apply]
        simp only [startCompleteVertexLabel_eq_offset (hX j)]
      _ = 0 := w.property.2

end PaperP1.HeavyPhysicalRelations
