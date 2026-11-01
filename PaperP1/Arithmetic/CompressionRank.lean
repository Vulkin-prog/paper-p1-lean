module

public import PaperP1.Arithmetic.NormalizedUnitCount
public import PaperP1.Arithmetic.PrivateEvenImages

/-! # Finite rank of a normalized pair and the exact dependence criterion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressionRank

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

local instance compressionRankPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem private_local_ranks {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L)) :
    Module.finrank F₂ (squareClassSpace x L) = L ∧ Module.finrank F₂ (squareClassSpace y L) = L := by
  constructor
  · rw [← space_normalized hb hx, FiniteEvenSquareClasses.finrank_space _ (hprivate.mono subset_union_left),
      card_normalized hb (by omega), Nat.add_sub_cancel]
  · rw [← space_normalized ha hy, FiniteEvenSquareClasses.finrank_space _ (hprivate.mono subset_union_right),
      card_normalized ha (by omega), Nat.add_sub_cancel]

theorem dependent_two_units {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L))
    (hdep : ¬Disjoint (squareClassSpace x L) (squareClassSpace y L)) : 2 ≤ (units a b x y L).card := by
  have hdep' : ¬Disjoint (FiniteEvenSquareClasses.space (normalized b x L))
      (FiniteEvenSquareClasses.space (normalized a y L)) := by
    rw [space_normalized hb hx, space_normalized ha hy]
    exact hdep
  have hcard := PrivateEvenImages.two_le_inter_card (normalized b x L) (normalized a y L) hprivate hdep'
  rwa [normalized_intersection_card ha hb (by omega) (by omega)] at hcard

theorem units_intersection_nonempty {a b x y L : ℕ} (hunits : (units a b x y L).Nonempty) :
    (normalized b x L ∩ normalized a y L).Nonempty := by
  obtain ⟨u, hu⟩ := hunits
  refine ⟨b * Affine.startCompleteVertexLabel x L u.1, mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact mem_image.mpr ⟨_, mem_values.mpr ⟨u.1, rfl⟩, rfl⟩
  · exact mem_image.mpr ⟨_, mem_values.mpr ⟨u.2, rfl⟩, (mem_units.mp hu).symm⟩

theorem rank_lower_bound {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hinter : (normalized b x L ∩ normalized a y L).Nonempty)
    (hprivate : FiniteEvenSquareClasses.Private (union a b x y L)) :
    (2 - 1 / (b : ℝ)) * L - 1 ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) : ℝ) := by
  have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
  rw [card_normalized hb (by omega), card_normalized ha (by omega)] at hcard
  change (union a b x y L).card + (normalized b x L ∩ normalized a y L).card = (L + 1) + (L + 1) at hcard
  have hcardR : ((union a b x y L).card : ℝ) + (normalized b x L ∩ normalized a y L).card = 2 * (L + 1) := by
    have h : (union a b x y L).card + (normalized b x L ∩ normalized a y L).card = 2 * (L + 1) := by omega
    exact_mod_cast h
  have hU : 1 ≤ (union a b x y L).card := by
    apply card_pos.mpr
    exact (normalized_nonempty b x L).mono subset_union_left
  have hrank := rank_union ha hb hx hy hinter hprivate
  have hrankR : (Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) : ℝ) =
      ((union a b x y L).card : ℝ) - 1 := by rw [hrank, Nat.cast_sub hU, Nat.cast_one]
  have hbound := intersection_card_bound (L := L) ha hb hab (by omega : 0 < x) (by omega : 0 < y)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbound' : ((normalized b x L ∩ normalized a y L).card : ℝ) ≤ ((L : ℝ) + 1) / b + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbound
  rw [hrankR]
  have hcalc : ((L : ℝ) + 1) / b = (1 / (b : ℝ)) * L + 1 / b := by ring
  have hinv : 1 / (b : ℝ) ≤ 1 := (div_le_one hbR).mpr hb1
  rw [hcalc] at hbound'
  nlinarith

end PaperP1.CompressionRank
