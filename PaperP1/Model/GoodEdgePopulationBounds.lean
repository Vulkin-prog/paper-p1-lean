module

public import PaperP1.Model.RetainedIndependentDeficitComparison
public import PaperP1.Arithmetic.FixedChannelLinearCount

/-! # Explicit linear-size bounds for the actual good-edge population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgePopulationBounds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.GoodEdgeCompression

theorem cardinal {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) :
    (goodEdges H N L).card ≤ 26 * (L + 1) * N := by
  have hA : (PrivateChannelActivity.pairs N 0 2 3 L).card ≤ 11 * (L + 1) * N := by
    calc
      _ ≤ (PrivateChannelSources.goodSources N 0 2 3 L).card := card_image_le
      _ ≤ (FixedChannelSourceGeometry.unitSources N 2 3 L).card :=
        card_le_card (PrivateChannelSources.good_sources_subset_unitSources N 0 2 3 L)
      _ ≤ _ := by
        simpa using FixedChannelLinearCount.unit_sources_card_linear
          (N := N) (a := 2) (b := 3) (L := L) (by omega) (by omega)
  have hB : (PrivateChannelActivity.pairs N 0 3 4 L).card ≤ 15 * (L + 1) * N := by
    calc
      _ ≤ (PrivateChannelSources.goodSources N 0 3 4 L).card := card_image_le
      _ ≤ (FixedChannelSourceGeometry.unitSources N 3 4 L).card :=
        card_le_card (PrivateChannelSources.good_sources_subset_unitSources N 0 3 4 L)
      _ ≤ _ := by
        simpa using FixedChannelLinearCount.unit_sources_card_linear
          (N := N) (a := 3) (b := 4) (L := L) (by omega) (by omega)
  have hh := (card_le_card (RetainedIndependentDeficitComparison.good_subset_zero_channels (L := L) hN H)).trans
    (card_union_le _ _)
  nlinarith only [hh, hA, hB]

theorem independent_mass_bound {N L : ℕ} (hN : 2 ≤ N) (H : ℝ)
    (r : ℕ → ℝ) (p : ℝ)
    (hr : ∀ x ∈ dyadicBlock N, 0 ≤ r x ∧ r x ≤ p) :
    (∑ e ∈ goodEdges H N L, ∏ x ∈ e, r x) ≤ (26 * (L + 1) * N : ℕ) * p ^ 2 := by
  have hpoint (e : Finset ℕ) (he : e ∈ goodEdges H N L) : (∏ x ∈ e, r x) ≤ p ^ 2 := by
    have hsub := (RetainedGoodEdges.good_pair_regular hN e he).trans
      (RegularStarts.regularStarts_subset N L)
    calc
      _ ≤ ∏ _x ∈ e, p := prod_le_prod₀ (fun x hx ↦ (hr x (hsub hx)).1)
        (fun x hx ↦ (hr x (hsub hx)).2)
      _ = _ := by rw [prod_const, RetainedGoodEdges.good_pair_card H N L e he]
  calc
    _ ≤ ∑ _e ∈ goodEdges H N L, p ^ 2 := sum_le_sum hpoint
    _ = ((goodEdges H N L).card : ℝ) * p ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast cardinal hN H) (sq_nonneg p)

end PaperP1.GoodEdgePopulationBounds
