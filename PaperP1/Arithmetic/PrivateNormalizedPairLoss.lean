module

public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Arithmetic.GoodEdgeCompression

/-! # Exact full relation loss for every private normalized pair

The equality includes the empty-coincidence case. No geometric channel,
coprimality or asymptotic hypothesis is needed for this finite statement.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateNormalizedPairLoss

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss

local instance privateLossPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem kernel_rank_zero {S : Finset ℕ} (hprivate : FiniteEvenSquareClasses.Private S) :
    Module.finrank F₂ (PaperP1.FiniteResidualRank.valueKernel S) = 0 := by
  have hker := LinearMap.ker_eq_bot.mpr (FiniteEvenSquareClasses.combination_injective S hprivate)
  change Module.finrank F₂ (LinearMap.ker (EvenImage.combination (K := F₂) (FiniteEvenSquareClasses.data S))) = 0
  rw [hker, finrank_bot]

theorem loss_eq_units_nonempty {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hunits : (units a b x y L).Nonempty)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    pairLoss x y L = (units a b x y L).card - 1 := by
  have hrank := rank_union ha hb hx hy (PaperP1.CompressionRank.units_intersection_nonempty hunits) hprivate
  have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
  rw [card_normalized hb (by omega), card_normalized ha (by omega),
    normalized_intersection_card ha hb (by omega) (by omega)] at hcard
  change (NormalizedWindowSets.union a b x y L).card + (units a b x y L).card = (L + 1) + (L + 1) at hcard
  have hUpos : 0 < (NormalizedWindowSets.union a b x y L).card :=
    card_pos.mpr ((normalized_nonempty b x L).mono subset_union_left)
  have hum : 0 < (units a b x y L).card := hunits.card_pos
  unfold pairLoss
  rw [hrank]
  omega

theorem loss_eq_units {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    pairLoss x y L = (units a b x y L).card - 1 := by
  classical
  by_cases hu : (units a b x y L).Nonempty
  · exact loss_eq_units_nonempty ha hb hx hy hu hprivate
  · have hz : (units a b x y L).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hu)
    have hbound := loss_le_units_add_residual_all (L := L) ha hb hx hy
    rw [kernel_rank_zero hprivate, hz] at hbound
    rw [hz]
    omega

theorem loss_eq_units_privateAbove {H : ℝ} {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : PaperP1.GoodEdgeCompression.PrivateAbove H (NormalizedWindowSets.union a b x y L)) :
    pairLoss x y L = (units a b x y L).card - 1 :=
  loss_eq_units ha hb hx hy hprivate.private

end PaperP1.PrivateNormalizedPairLoss
