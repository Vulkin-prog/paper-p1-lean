module

public import PaperP1.Arithmetic.ActualNormalizedMatches
public import PaperP1.Arithmetic.NormalizedPairGeometry
public import PaperP1.Arithmetic.CompressionRank

/-! # True scaled old/new value sets and their exact matching cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledTargetValues

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.ActualNormalizedMatches

local instance scaledTargetPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def oldValues (a b c x y L : ℕ) : Finset ℕ := FiniteEvenSquareClasses.dilate c (NormalizedWindowSets.union a b x y L)

def newValues (a b d z L : ℕ) : Finset ℕ := normalized (a * b * d) z L

def allValues (a b c d x y z L : ℕ) : Finset ℕ := oldValues a b c x y L ∪ newValues a b d z L

theorem normalized_positive {q x L : ℕ} (hq : 0 < q) (hx : 2 ≤ x) : ∀ n ∈ normalized q x L, 0 < n := by
  intro n hn
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
  exact Nat.mul_pos hq (values_positive hx v hv)

theorem union_positive {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    ∀ n ∈ NormalizedWindowSets.union a b x y L, 0 < n := by
  intro n hn
  rcases mem_union.mp hn with hn | hn
  · exact normalized_positive hb hx n hn
  · exact normalized_positive ha hy n hn

theorem old_space {a b c x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hunits : (NormalizedUnitCount.units a b x y L).Nonempty) :
    FiniteEvenSquareClasses.space (oldValues a b c x y L) = squareClassSpace x L ⊔ squareClassSpace y L := by
  rw [oldValues, FiniteEvenSquareClasses.space_dilate _ hc (union_positive ha hb hx hy)]
  exact space_union ha hb hx hy (CompressionRank.units_intersection_nonempty hunits)

theorem new_space {a b d z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hz : 2 ≤ z) :
    FiniteEvenSquareClasses.space (newValues a b d z L) = squareClassSpace z L :=
  space_normalized (Nat.mul_pos (Nat.mul_pos ha hb) hd) hz

theorem new_card {a b d z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hz : 0 < z) :
    (newValues a b d z L).card = L + 1 :=
  card_normalized (Nat.mul_pos (Nat.mul_pos ha hb) hd) hz

theorem intersection_card {a b c d x y z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hz : 0 < z) :
    (exactOffsets a b c d x y z L).card = (oldValues a b c x y L ∩ newValues a b d z L).card := by
  have hscale : 0 < a * b * d := Nat.mul_pos (Nat.mul_pos ha hb) hd
  apply card_bij (fun k _ ↦ a * b * d * startCompleteVertexLabel z L k)
  · intro k hk
    obtain ⟨n, hn, heq⟩ := mem_exactOffsets.mp hk
    apply mem_inter.mpr
    refine ⟨mem_image.mpr ⟨n, hn, heq.symm⟩, ?_⟩
    exact mem_image.mpr ⟨_, mem_values.mpr ⟨k, rfl⟩, rfl⟩
  · intro k _ j _ heq
    exact startCompleteVertexLabel_injective hz (mul_left_cancel₀ hscale.ne' heq)
  · intro n hn
    obtain ⟨hold, hnew⟩ := mem_inter.mp hn
    obtain ⟨m, hm, hmEq⟩ := mem_image.mp hold
    obtain ⟨v, hv, hvEq⟩ := mem_image.mp hnew
    obtain ⟨k, hkEq⟩ := mem_values.mp hv
    have hvalue : a * b * d * startCompleteVertexLabel z L k = n := by rw [hkEq]; exact hvEq
    exact ⟨k, mem_exactOffsets.mpr ⟨m, hm, hvalue.trans hmEq.symm⟩, hvalue⟩

theorem all_card_le {a b c d x y z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (allValues a b c d x y z L).card ≤ 3 * (L + 1) := by
  have hunion := card_union_le (oldValues a b c x y L) (newValues a b d z L)
  have hold : (oldValues a b c x y L).card ≤ (NormalizedWindowSets.union a b x y L).card := card_image_le
  have hsource := NormalizedPairGeometry.union_card_le (L := L) ha hb hx hy
  have hnew := new_card (L := L) ha hb hd hz
  change (oldValues a b c x y L ∪ newValues a b d z L).card ≤ _
  omega

end PaperP1.ScaledTargetValues
