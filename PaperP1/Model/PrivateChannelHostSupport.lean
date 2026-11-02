module

public import PaperP1.Model.SelectedPairCumulantLower
public import PaperP1.Model.PrivateChannelSources

/-! # Every actual private fixed-channel source is a distinct full-loss host -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelHostSupport

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.PrivateChannelSources PaperP1.SelectedPairCumulantLower

local instance privateChannelHostTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem loss_positive_of_two_units {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hunits : 2 ≤ (units a b x y L).card)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L)) :
    0 < pairLoss x y L := by
  have hunonempty : (units a b x y L).Nonempty := card_pos.mp (by omega)
  have hinter := CompressionRank.units_intersection_nonempty hunonempty
  have hrank := rank_union ha hb hx hy hinter hprivate
  have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
  rw [card_normalized hb (by omega), card_normalized ha (by omega),
    normalized_intersection_card ha hb (by omega) (by omega)] at hcard
  change (union a b x y L).card + (units a b x y L).card = (L + 1) + (L + 1) at hcard
  have hU : 1 ≤ (union a b x y L).card := card_pos.mpr
    ((normalized_nonempty b x L).mono subset_union_left)
  unfold pairLoss
  omega

theorem good_sources_subset_hosts {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a)
    (hab : a < b) (hlarge : (a + b) * (L + 1) < N) :
    goodSources N H a b L ⊆ distinctHosts N L := by
  intro p hp
  obtain ⟨hx, hy, hu, hprivate⟩ := mem_goodSources.mp hp
  have horder := good_sources_order hN hab hlarge hp
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ?_⟩, horder.ne⟩
  exact loss_positive_of_two_units ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
    (hN.trans (mem_Ico.mp hy).1) hu hprivate.private

theorem channel_sources_subset_hosts {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a)
    (hab : a < b) (hlarge : (a + b) * (L + 1) < N) :
    channelSources N H a b L ⊆ distinctHosts N L := by
  intro p hp
  obtain hp | hp := mem_union.mp hp
  · exact good_sources_subset_hosts hN ha hab hlarge hp
  · obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact (swap_mem_distinctHosts N L q).mpr (good_sources_subset_hosts hN ha hab hlarge hq)

theorem channel_cumulant_lower {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a)
    (hab : a < b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    channelMass N H a b L - PairHostIndependentMass.mass N L -
        HeterogeneousBernoulli.powerSum (dyadicBlock N)
          (fun x ↦ Model.InfiniteStarts.infiniteMarginal x L) 2 ≤
      RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L :=
  second_cumulant_lower hN hL (channelSources N H a b L)
    (channel_sources_subset_hosts hN ha hab hlarge)

end PaperP1.PrivateChannelHostSupport
