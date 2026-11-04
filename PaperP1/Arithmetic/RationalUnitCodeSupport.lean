module

public import PaperP1.Arithmetic.RationalUnitCode
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Exact support and domination of the global rational even-unit code

A nonzero rational code forces an actual small geometric channel.
On an aligned pair its nullity is dominated by the full actual pair loss.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalUnitCodeSupport

open Finset PaperP1.Arithmetic PaperP1.RationalUnitCode PaperP1.NormalizedUnitCount
  PaperP1.NormalizedPairRankLoss PaperP1.NormalizedWindowSets PaperP1.EnlargedPairGeometry

local instance rationalUnitSupportPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem small_height_bound {L : ℕ} (hL : 0 < L) : 2 * (L + 1) ≤ (L + 1) ^ 3 := by
  have hB : 2 ≤ L + 1 := by omega
  have hh := Nat.mul_le_mul_right (L + 1) hB
  have hsq : L + 1 ≤ (L + 1) ^ 2 := le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 2 ≠ 0)
  have hm := Nat.mul_le_mul_left (L + 1) hsq
  nlinarith only [hh, hm]

theorem nullity_zero_of_no_channel {x y L : ℕ} (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (hno : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      ¬Geometric a b x y L) : nullity x y L = 0 := by
  have hinj : Function.Injective (ratio x y L) := by
    intro u v huv
    by_contra hne
    have hcross := (ratio_eq_iff (by omega : 2 ≤ y) u v).mp huv
    obtain ⟨a, b, ha, hb, hab, haB, hbB, hu, _hv⟩ := PaperP1.SmallExactUnitAlignment.two_units x y L hx hy
      u.1 v.1 u.2 v.2 hne hcross
    exact hno a b ha hb hab (haB.trans (small_height_bound hL)) (hbB.trans (small_height_bound hL))
      (PaperP1.ExactUnitGeometric.of_unit (by omega : 0 < x) (by omega : 0 < y) hu)
  unfold nullity code
  rw [PaperP1.FiberEvenCode.code_eq_bot_of_injective hinj, finrank_bot]

theorem weight_zero_of_no_channel {x y L : ℕ} (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (hno : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      ¬Geometric a b x y L) : PaperP1.RationalUnitCode.weight x y L = 0 := by
  rw [PaperP1.RationalUnitCode.weight, nullity_zero_of_no_channel hL hx hy hno, pow_zero, sub_self]

theorem units_le_full_loss {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (units a b x y L).card - 1 ≤ pairLoss x y L := by
  classical
  by_cases hu : (units a b x y L).Nonempty
  · have hinter := PaperP1.CompressionRank.units_intersection_nonempty hu
    have hrank : Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L) ≤
        (NormalizedWindowSets.union a b x y L).card - 1 := by
      rw [← space_union ha hb hx hy hinter]
      have hh := LinearMap.finrank_range_le
        (PaperP1.EvenImage.evenMap (K := F₂) (PaperP1.FiniteEvenSquareClasses.data (NormalizedWindowSets.union a b x y L)))
      rw [PaperP1.EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at hh
      exact hh
    have hcard := card_union_add_card_inter (normalized b x L) (normalized a y L)
    rw [card_normalized hb (by omega), card_normalized ha (by omega),
      normalized_intersection_card ha hb (by omega) (by omega)] at hcard
    change (NormalizedWindowSets.union a b x y L).card + (units a b x y L).card = (L + 1) + (L + 1) at hcard
    have hum := hu.card_pos
    have hU : 0 < (NormalizedWindowSets.union a b x y L).card :=
      card_pos.mpr ((normalized_nonempty b x L).mono subset_union_left)
    unfold pairLoss
    omega
  · have hz : (units a b x y L).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hu)
    rw [hz]
    exact Nat.zero_le _

theorem nullity_le_full_loss {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3)
    (hlarge : 4 * (L + 1) ^ 7 < y) (hg : Geometric a b x y L) :
    nullity x y L ≤ pairLoss x y L := by
  rw [nullity_eq_units ha hb hab hL hx hy haB hbB hlarge hg]
  exact units_le_full_loss ha hb (by omega) (by omega)

theorem weight_le_full {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hL : 0 < L) (hx : L + 1 < x) (hy : L + 1 < y)
    (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3)
    (hlarge : 4 * (L + 1) ^ 7 < y) (hg : Geometric a b x y L) :
    PaperP1.RationalUnitCode.weight x y L ≤ (2 ^ pairLoss x y L : ℝ) - 1 := by
  unfold PaperP1.RationalUnitCode.weight
  exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (nullity_le_full_loss ha hb hab hL hx hy haB hbB hlarge hg)) 1

end PaperP1.RationalUnitCodeSupport
