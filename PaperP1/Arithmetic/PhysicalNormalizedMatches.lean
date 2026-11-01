module

public import PaperP1.Arithmetic.ActualNormalizedMatches
public import PaperP1.Model.CompatibleWindowOverlap

/-! # Physical fractions count true window overlap and one other exact-unit family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalNormalizedMatches

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount
  PaperP1.ActualNormalizedMatches

local instance physicalMatchDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem same_dilation_intersection {q x z L : ℕ} (hq : 0 < q) :
    (normalized q z L ∩ normalized q x L).card = (values z L ∩ values x L).card := by
  unfold normalized FiniteEvenSquareClasses.dilate
  rw [← image_inter _ _ (mul_right_injective₀ hq.ne'), card_image_of_injective _ (mul_right_injective₀ hq.ne')]

theorem physical_card {a b c q x y z L : ℕ} (hc : 0 < c) (hq : 0 < q) (hz : 0 < z)
    (hfactor : a * b = c * q) :
    (exactOffsets a b c 1 x y z L).card = (normalized q z L ∩ union a b x y L).card := by
  apply card_bij (fun k _ ↦ q * startCompleteVertexLabel z L k)
  · intro k hk
    obtain ⟨n, hn, heq⟩ := mem_exactOffsets.mp hk
    have hvalue : q * startCompleteVertexLabel z L k = n := by
      apply mul_left_cancel₀ hc.ne'
      calc
        c * (q * startCompleteVertexLabel z L k) = a * b * 1 * startCompleteVertexLabel z L k := by rw [hfactor]; ring
        _ = c * n := heq
    exact mem_inter.mpr ⟨mem_image.mpr ⟨_, mem_values.mpr ⟨k, rfl⟩, rfl⟩, hvalue ▸ hn⟩
  · intro k _ j _ heq
    exact startCompleteVertexLabel_injective hz (mul_left_cancel₀ hq.ne' heq)
  · intro n hn
    obtain ⟨hnorm, hU⟩ := mem_inter.mp hn
    change n ∈ (values z L).image (fun v ↦ q * v) at hnorm
    obtain ⟨v, hv, hvEq⟩ := mem_image.mp hnorm
    obtain ⟨k, hkEq⟩ := mem_values.mp hv
    have hvalue : q * startCompleteVertexLabel z L k = n := by rw [hkEq]; exact hvEq
    refine ⟨k, mem_exactOffsets.mpr ⟨n, hU, ?_⟩, hvalue⟩
    calc
      _ = c * (q * startCompleteVertexLabel z L k) := by rw [hfactor]; ring
      _ = c * n := congrArg (fun v ↦ c * v) hvalue

theorem intersection_union (S T U : Finset ℕ) : S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U) := by
  ext n
  simp only [mem_inter, mem_union, and_or_left]

theorem physical_a_bound {a b x y z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hy : 0 < y) (hz : 0 < z) (hoverlap : (values z L ∩ values x L).card ≤ 1) :
    ((exactOffsets a b a 1 x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b + 2 := by
  rw [physical_card ha hb hz rfl, NormalizedWindowSets.union, intersection_union]
  have hcard := card_union_le (normalized b z L ∩ normalized b x L) (normalized b z L ∩ normalized a y L)
  have hcardR : (((normalized b z L ∩ normalized b x L) ∪ (normalized b z L ∩ normalized a y L)).card : ℝ) ≤
      (normalized b z L ∩ normalized b x L).card + (normalized b z L ∩ normalized a y L).card := by exact_mod_cast hcard
  have hsmall : ((normalized b z L ∩ normalized b x L).card : ℝ) ≤ 1 := by
    rw [same_dilation_intersection hb]
    exact_mod_cast hoverlap
  have hother := intersection_card_bound (L := L) ha hb hab hz hy
  linarith

theorem physical_b_bound {a b x y z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 0 < x) (hz : 0 < z) (hoverlap : (values z L ∩ values y L).card ≤ 1) :
    ((exactOffsets a b b 1 x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b + 2 := by
  rw [physical_card hb ha hz (Nat.mul_comm a b), NormalizedWindowSets.union, intersection_union]
  have hcard := card_union_le (normalized a z L ∩ normalized b x L) (normalized a z L ∩ normalized a y L)
  have hcardR : (((normalized a z L ∩ normalized b x L) ∪ (normalized a z L ∩ normalized a y L)).card : ℝ) ≤
      (normalized a z L ∩ normalized b x L).card + (normalized a z L ∩ normalized a y L).card := by exact_mod_cast hcard
  have hsmall : ((normalized a z L ∩ normalized a y L).card : ℝ) ≤ 1 := by
    rw [same_dilation_intersection ha]
    exact_mod_cast hoverlap
  have hother := intersection_card_bound (L := L) ha hb hab hx hz
  rw [inter_comm (normalized b x L) (normalized a z L)] at hother
  linarith

end PaperP1.PhysicalNormalizedMatches
