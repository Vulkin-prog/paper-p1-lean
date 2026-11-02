module

public import PaperP1.Probability.ActiveFamilyCover
public import PaperP1.Model.ActiveEdgeObservables
public import PaperP1.Model.ExactContactEdges

/-! # Actual activation probability depends only on positive-mass members -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualActiveFamilyCover

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ActiveEdgeObservables

theorem probability_mono {M L : ℕ} (F T : Finset (Finset ℕ))
    (hFcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M) (hTcut : ∀ e ∈ T, ∀ x ∈ e, x + L ≤ M)
    (hcover : ∀ e ∈ F, 0 < infiniteJointMoment L e → e ∈ T) : probability F L ≤ probability T L := by
  rw [probability_eq_finite F hFcut, probability_eq_finite T hTcut]
  apply ActiveFamilyCover.activation_mono
  intro e he hq
  apply hcover e he
  rwa [← infiniteJointMoment_eq_finite M L e (hFcut e he)] at hq

theorem close_probability_eq_exact (N L : ℕ) (hL : 0 < L) :
    probability (ClosePairs.pairs (dyadicBlock N) L) L = probability (ExactContactEdges.edges N L) L := by
  let M := dyadicCutoff N L
  have hcut : ∀ e ∈ (dyadicBlock N).powersetCard 2, ∀ x ∈ e, x + L ≤ M := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff (subset_refl (dyadicBlock N)) x ((mem_powersetCard.mp he).1 hx)
  apply le_antisymm
  · apply probability_mono _ _
      (fun e he ↦ hcut e (ClosePairs.subset (dyadicBlock N) L he))
      (fun e he ↦ hcut e (ExactContactEdges.subset_pairs N L hL he))
    intro e he hq
    obtain ⟨x, y, hx, hy, hxy, hyL, rfl⟩ := ClosePairs.data (dyadicBlock N) L e he
    have heq := ContactFamilySeeds.positive_exact hL hxy hyL hq
    apply mem_image.mpr
    exact ⟨x, mem_filter.mpr ⟨hx, heq ▸ hy⟩, by rw [heq]⟩
  · exact probability_mono _ _
      (fun e he ↦ hcut e (ExactContactEdges.subset_pairs N L hL he))
      (fun e he ↦ hcut e (ClosePairs.subset (dyadicBlock N) L he))
      (fun _ he _ ↦ ExactContactEdges.subset_close N L hL he)

end PaperP1.ActualActiveFamilyCover
