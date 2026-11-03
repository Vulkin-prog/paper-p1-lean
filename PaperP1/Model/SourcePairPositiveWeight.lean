module

public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Model.PrivateChannelSources
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Positive source relation weight with local kernels retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairPositiveWeight

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.NormalizedPairRankLoss PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount
  PaperP1.PrivateChannelSources PaperP1.SubspaceFamilyRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def weight (x y L : ℕ) : ℝ := (2 ^ pairLoss x y L : ℝ) - 1

def setWeight (L : ℕ) (e : Finset ℕ) : ℝ :=
  (2 ^ (e.card * L - Module.finrank F₂ (span (fun z ↦ squareClassSpace z L) e)) : ℝ) - 1

theorem weight_nonneg (x y L : ℕ) : 0 ≤ weight x y L :=
  sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem setWeight_nonneg (L : ℕ) (e : Finset ℕ) : 0 ≤ setWeight L e :=
  sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem weight_comm (x y L : ℕ) : weight x y L = weight y x L := by
  unfold weight
  rw [pairLoss_comm]

theorem setWeight_pair {x y : ℕ} (hxy : x ≠ y) (L : ℕ) :
    setWeight L {x, y} = weight x y L := by
  unfold setWeight weight pairLoss
  have hspan : span (fun z ↦ squareClassSpace z L) {x, y} = squareClassSpace x L ⊔ squareClassSpace y L := by
    rw [span_insert]
    simp [span]
  rw [card_pair hxy, hspan]

theorem private_loss_eq {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hu : (units a b x y L).Nonempty)
    (hp : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    pairLoss x y L = (units a b x y L).card - 1 := by
  have hrank := rank_union ha hb hx hy (CompressionRank.units_intersection_nonempty hu) hp
  have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
  rw [card_normalized hb (by omega), card_normalized ha (by omega),
    normalized_intersection_card ha hb (by omega) (by omega)] at hcard
  change (NormalizedWindowSets.union a b x y L).card + (units a b x y L).card = (L + 1) + (L + 1) at hcard
  have hU : 1 ≤ (NormalizedWindowSets.union a b x y L).card := card_pos.mpr
    ((normalized_nonempty b x L).mono subset_union_left)
  have hu1 : 1 ≤ (units a b x y L).card := hu.card_pos
  unfold pairLoss
  rw [hrank]
  omega

theorem good_source_loss {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    {xy : ℕ × ℕ} (hxy : xy ∈ goodSources N H a b L) :
    pairLoss xy.1 xy.2 L = (units a b xy.1 xy.2 L).card - 1 := by
  obtain ⟨hx, hy, hu, hp⟩ := mem_goodSources.mp hxy
  exact private_loss_eq ha hb (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1)
    (card_pos.mp (by omega)) hp.private

end PaperP1.SourcePairPositiveWeight
