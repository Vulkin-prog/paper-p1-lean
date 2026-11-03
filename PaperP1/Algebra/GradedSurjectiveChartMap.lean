module

public import PaperP1.Algebra.GradedDehomogenization

/-! # Surjectivity of a graded ring map descends to the actual degree-one charts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedSurjectiveChartMap

open HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]

theorem away_map_surjective (f : G →+*ᵍ H) (hf : Function.Surjective f)
    {b : A} (hb : b ∈ G 1) : Function.Surjective (Away.map f b) := by
  intro z
  obtain ⟨y, rfl⟩ := GradedDehomogenization.map_surjective H (f.map_mem hb) z
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨GradedDehomogenization.map G hb x, DFunLike.congr_fun (GradedDehomogenization.map_natural G hb f) x⟩

theorem homogeneous_preimage (f : G →+*ᵍ H) (hf : Function.Surjective f)
    (n : ℕ) (y : B) (hy : y ∈ H n) : ∃ x : A, x ∈ G n ∧ f x = y := by
  obtain ⟨x, hx⟩ := hf y
  refine ⟨(DirectSum.decompose G x n : A), (DirectSum.decompose G x n).property, ?_⟩
  rw [f.map_directSumDecompose, hx]
  exact DirectSum.decompose_of_mem_same H hy

end PaperP1.GradedSurjectiveChartMap
