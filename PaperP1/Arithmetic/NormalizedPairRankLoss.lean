module

public import PaperP1.Algebra.EvenImageDefect
public import PaperP1.Algebra.FiniteSetValueSpan
public import PaperP1.Arithmetic.FiniteResidualRank
public import PaperP1.Arithmetic.CompressionRank
public import PaperP1.Model.FreeComponentRank

/-! # Exact units and the residual value kernel bound the actual pair rank loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedPairRankLoss

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount
  PaperP1.FiniteResidualRank

local instance pairLossPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def pairLoss (x y L : ℕ) : ℕ := 2 * L - Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)

theorem pairLoss_comm (x y L : ℕ) : pairLoss x y L = pairLoss y x L := by
  have heq : squareClassSpace x L ⊔ squareClassSpace y L = squareClassSpace y L ⊔ squareClassSpace x L := sup_comm _ _
  unfold pairLoss
  rw [heq]

theorem intersection_rank_le_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    FreeComponentRank.pairIntersectionRank x y L ≤ pairLoss x y L := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hxrank := LocalRunRank.squareClass_rank_le x L hx
  have hyrank := LocalRunRank.squareClass_rank_le y L hy
  unfold FreeComponentRank.pairIntersectionRank pairLoss
  omega

theorem dimension_le_space_add_kernel (S : Finset ℕ) :
    S.card - 1 ≤ Module.finrank F₂ (FiniteEvenSquareClasses.space S) + Module.finrank F₂ (valueKernel S) := by
  have h := EvenImageDefect.dimension_le_image_add_kernel (K := F₂) (FiniteEvenSquareClasses.data S)
  rw [Fintype.card_coe] at h
  exact h

theorem loss_le_units_add_residual {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hunits : (units a b x y L).Nonempty) :
    pairLoss x y L ≤ (units a b x y L).card - 1 +
      Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) := by
  have hinter := CompressionRank.units_intersection_nonempty hunits
  have hrank := dimension_le_space_add_kernel (NormalizedWindowSets.union a b x y L)
  rw [space_union ha hb hx hy hinter] at hrank
  have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
  rw [card_normalized hb (by omega : 0 < x), card_normalized ha (by omega : 0 < y),
    normalized_intersection_card ha hb (by omega : 0 < x) (by omega : 0 < y)] at hcard
  have hUpos : 0 < (NormalizedWindowSets.union a b x y L).card := by
    apply card_pos.mpr
    exact (normalized_nonempty b x L).mono subset_union_left
  have hu : 0 < (units a b x y L).card := hunits.card_pos
  unfold pairLoss
  change (NormalizedWindowSets.union a b x y L).card + (units a b x y L).card = (L + 1) + (L + 1) at hcard
  omega

theorem loss_le_units_add_residual_all {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    pairLoss x y L ≤ (units a b x y L).card - 1 +
      Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) := by
  by_cases hunits : (units a b x y L).Nonempty
  · exact loss_le_units_add_residual ha hb hx hy hunits
  · have hu0 : (units a b x y L).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hunits)
    have hfull := FiniteSetValueSpan.rank_add_kernel (K := F₂) parityVec (NormalizedWindowSets.union a b x y L)
    change Module.finrank F₂ (FiniteSetValueSpan.span (K := F₂) parityVec (NormalizedWindowSets.union a b x y L)) +
      Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) = _ at hfull
    have htwo := FiniteSetValueSpan.full_union_rank_le_two_even_add_two (K := F₂) parityVec
      (normalized b x L) (normalized a y L) (normalized_nonempty b x L) (normalized_nonempty a y L)
    change Module.finrank F₂ (FiniteSetValueSpan.span (K := F₂) parityVec (NormalizedWindowSets.union a b x y L)) ≤
      Module.finrank F₂ ↥(FiniteEvenSquareClasses.space (normalized b x L) ⊔ FiniteEvenSquareClasses.space (normalized a y L)) + 2 at htwo
    rw [space_normalized hb hx, space_normalized ha hy] at htwo
    have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
    rw [card_normalized hb (by omega : 0 < x), card_normalized ha (by omega : 0 < y),
      normalized_intersection_card ha hb (by omega : 0 < x) (by omega : 0 < y), hu0] at hcard
    change (NormalizedWindowSets.union a b x y L).card + 0 = (L + 1) + (L + 1) at hcard
    unfold pairLoss
    rw [hu0]
    omega

end PaperP1.NormalizedPairRankLoss
