module

public import PaperP1.Arithmetic.TernaryTopProducts
public import PaperP1.Combinatorics.TopProductSelection

/-! # The actual maximizing selection consists of the k strictly largest groups -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryLargestSelection

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts

theorem attained_largest (U : Fin 3 → Finset ℕ) (H k : ℕ)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hp : 0 < topProduct U H k) :
    ∃ S ⊆ active U H, S.card = k ∧ topProduct U H k = ∏ u ∈ S, group H u ∧
      ∀ u ∈ S, ∀ v ∈ active U H \ S, group H v < group H u := by
  obtain ⟨S, hsub, hcard, hprod⟩ := attained U H k hp
  refine ⟨S, hsub, hcard, hprod, ?_⟩
  intro u hu v hv
  have hvG := (mem_sdiff.mp hv).1
  have hvS := (mem_sdiff.mp hv).2
  have hle : group H v ≤ group H u := TopProductSelection.outside_le_selected
    (active U H) S (group H) k (fun w _ ↦ group_pos H w)
    (mem_powersetCard.mpr ⟨hsub, hcard⟩) (by
      intro B hB
      obtain ⟨hBG, hBcard⟩ := mem_powersetCard.mp hB
      rw [← hprod]
      exact selected_le_top U H k B hBG hBcard) hvG hvS hu
  apply lt_of_le_of_ne hle
  intro heq
  have hvu : v = u := active_values_injective hwidth hvG (hsub hu) heq
  exact hvS (hvu ▸ hu)

end PaperP1.TernaryLargestSelection
