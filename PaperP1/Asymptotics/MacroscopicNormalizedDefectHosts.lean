module

public import PaperP1.Asymptotics.BoundedNormalizedDefectPairCount
public import PaperP1.Asymptotics.MacroscopicIntervalGeometry

/-! # Actual macroscopic normalized-defect pair hosts, uniformly in the lower-endpoint exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicNormalizedDefectHosts

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.EnlargedPairGeometry
  PaperP1.MacroscopicIntervalGeometry

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (M : ℕ) (δ : ℝ) (H a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((starts M δ) ×ˢ (starts M δ)).filter fun xy ↦ Geometric a b xy.1 xy.2 L ∧
    ∃ n ∈ PaperP1.NormalizedWindowSets.union a b xy.1 xy.2 L, HDefective H n

theorem subset_bounded {M H a b L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    pairs M δ H a b L ⊆ PaperP1.BoundedNormalizedDefectPairs.pairs M H a b L := by
  intro xy hxy
  obtain ⟨hblock, hg, hd⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Ico.mpr ⟨starts_pos hM hδ hx, (mem_starts_iff.mp hx).2⟩,
      mem_Ico.mpr ⟨starts_pos hM hδ hy, (mem_starts_iff.mp hy).2⟩⟩, hg, hd⟩

theorem uniform_count (C D : ℝ) (hD : 0 ≤ D) (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ δ : ℝ, 0 < δ → ∀ L H a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ Q →
      (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
      ((pairs M δ H a b L).card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨M₀, h⟩ := PaperP1.BoundedNormalizedDefectPairCount.uniform_bound C D hD Q ε hε
  refine ⟨M₀, ?_⟩
  intro M hM δ hδ L H a b hcrit ha hab hbQ hH
  have hc : ((pairs M δ H a b L).card : ℝ) ≤ (PaperP1.BoundedNormalizedDefectPairs.pairs M H a b L).card := by
    exact_mod_cast card_le_card (subset_bounded (by omega : 2 ≤ M) hδ)
  exact hc.trans (h M hM L H a b hcrit ha hab hbQ hH)

end PaperP1.MacroscopicNormalizedDefectHosts
