module

public import PaperP1.Asymptotics.AsymmetricComponentHostData
public import PaperP1.Asymptotics.SubsetComponentHostData
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # The actual asymmetric free components are supported on the literal target values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricSubsetComponents

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.PinnedGraphResolution

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem pins_subset {x y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H)
    (old : Finset ℕ) :
    SubsetEnvelopeGraph.pins x y H R old (NormalizedWindowSets.values y L) ⊆
      AsymmetricEnvelopeGraph.pins x y L H R hnew hamb old := by
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · exact mem_union_left _ hv
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
    apply mem_union_right
    apply mem_image.mpr
    refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    intro i he
    apply (mem_filter.mp hj).2
    rw [← he, target_label hy hnew hamb]
    exact NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩

theorem nontrivial_subset {x y L H R : ℕ} (hy : R < y) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H)
    (old : Finset ℕ) :
    AsymmetricComponentHostData.nontrivial x y L H R hnew hamb old ⊆
      SubsetComponentHostData.nontrivial x y H R old (NormalizedWindowSets.values y L) := by
  intro c hc
  obtain ⟨hpin, hsize⟩ := (AsymmetricComponentHostData.mem_nontrivial x y L H R hnew hamb old c).mp hc
  apply (SubsetComponentHostData.mem_nontrivial x y H R old (NormalizedWindowSets.values y L) c).mpr
  refine ⟨?_, hsize⟩
  rintro ⟨v, hv, he⟩
  exact hpin ⟨v, pins_subset hy hnew hamb old hv, he⟩

end PaperP1.AsymmetricSubsetComponents
