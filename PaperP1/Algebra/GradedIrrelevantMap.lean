module

public import PaperP1.Algebra.GradedSurjectiveChartMap
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Actual irrelevant ideals commute with surjective graded maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedIrrelevantMap

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H] (f : G →+*ᵍ H)

theorem map_le : (HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom ≤
    (HomogeneousIdeal.irrelevant H).toIdeal := by
  rw [Ideal.map_le_iff_le_comap, HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro a ha
  simp only [Set.mem_iUnion] at ha
  obtain ⟨n, hn, ha⟩ := ha
  exact HomogeneousIdeal.mem_irrelevant_of_mem H hn (f.map_mem ha)

theorem map_eq (hf : Function.Surjective f) :
    (HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom = (HomogeneousIdeal.irrelevant H).toIdeal := by
  apply le_antisymm (map_le f)
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨n, hn, hb⟩ := hb
  obtain ⟨a, ha, rfl⟩ := GradedSurjectiveChartMap.homogeneous_preimage f hf n b hb
  exact Ideal.mem_map_of_mem f.toRingHom (HomogeneousIdeal.mem_irrelevant_of_mem G hn ha)

end PaperP1.GradedIrrelevantMap
