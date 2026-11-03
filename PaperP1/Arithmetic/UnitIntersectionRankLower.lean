module

public import PaperP1.Arithmetic.EvenSubsetRankDefect
public import PaperP1.Arithmetic.PrivateEvenIntersection
public import PaperP1.Model.LocalRunRank

/-! # Every actual unit family has common effective dimension at least its even cardinality minus one local defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitIntersectionRankLower

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.FiniteEvenSquareClasses

local instance unitRankLowerPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem unit_count_le_local_defect {a b y z L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hy : 2 ≤ y) (hz : 2 ≤ z) :
    (units a b y z L).card ≤ Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) +
      Module.finrank F₂ (WindowRelationCode.windowRelationCode (y - 1) (L + 1)) + 1 := by
  have hsubset := EvenSubsetRankDefect.subset_defect
    (S := normalized b y L ∩ normalized a z L) (T := normalized b y L) inter_subset_left
  rw [card_normalized hb (by omega), space_normalized hb hy,
    normalized_intersection_card ha hb (by omega) (by omega)] at hsubset
  have hsub : space (normalized b y L ∩ normalized a z L) ≤
      space (normalized b y L) ⊓ space (normalized a z L) :=
    le_inf (PrivateEvenIntersection.space_mono inter_subset_left)
      (PrivateEvenIntersection.space_mono inter_subset_right)
  rw [space_normalized hb hy, space_normalized ha hz] at hsub
  have hmono := Submodule.finrank_mono hsub
  have hlocal := LocalRunRank.squareClass_rank_add_relation_rank (L := L) (x := y) (by omega)
  omega

theorem unit_count_le_intersection_add_two {a b y z L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hdefect : Module.finrank F₂ (WindowRelationCode.windowRelationCode (y - 1) (L + 1)) ≤ 1) :
    (units a b y z L).card ≤ Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) + 2 := by
  have h := unit_count_le_local_defect (L := L) ha hb hy hz
  omega

theorem intersection_lower {a b y z L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hy : 2 ≤ y) (hz : 2 ≤ z)
    (hdefect : Module.finrank F₂ (WindowRelationCode.windowRelationCode (y - 1) (L + 1)) ≤ 1) :
    (units a b y z L).card - 2 ≤ Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) := by
  have h := unit_count_le_intersection_add_two ha hb hy hz hdefect
  omega

end PaperP1.UnitIntersectionRankLower
