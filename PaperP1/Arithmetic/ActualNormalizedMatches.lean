module

public import PaperP1.Arithmetic.ExactMatchCongruences
public import PaperP1.Arithmetic.FixedChannelMatches

/-! # Only actual old normalized values supply target matching positions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualNormalizedMatches

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount
  PaperP1.UnionMatchDensity PaperP1.ExactMatchCongruences

local instance actualMatchDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def exactOffsets (a b c d x y z L : ℕ) : Finset (Fin (L + 1)) :=
  univ.filter fun k ↦ ∃ n ∈ union a b x y L,
    a * b * d * startCompleteVertexLabel z L k = c * n

def integerOffsets (a b c d x y z L : ℕ) : Finset ℤ :=
  (exactOffsets a b c d x y z L).image offset

theorem mem_exactOffsets {a b c d x y z L : ℕ} {k : Fin (L + 1)} :
    k ∈ exactOffsets a b c d x y z L ↔ ∃ n ∈ union a b x y L,
      a * b * d * startCompleteVertexLabel z L k = c * n := by
  simp only [exactOffsets, mem_filter, mem_univ, true_and]

theorem integerOffsets_card (a b c d x y z L : ℕ) :
    (integerOffsets a b c d x y z L).card = (exactOffsets a b c d x y z L).card := by
  rw [integerOffsets, card_image_of_injective _ (offset_injective L)]

theorem integerOffsets_subset {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i₀ j₀ : Fin (L + 1)) (h : ℤ)
    (hbaseX : startCompleteVertexLabel x L i₀ = a * t)
    (hbaseY : startCompleteVertexLabel y L j₀ = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) :
    integerOffsets a b c d x y z L ⊆ matchOffsets a b c d h (-1) L := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
  obtain ⟨n, hn, heq⟩ := mem_exactOffsets.mp hk
  have hinterval : offset k ∈ Ico (-1 : ℤ) (L : ℤ) := by
    rw [mem_Ico]
    unfold offset
    have hkL := k.isLt
    omega
  rcases mem_union.mp hn with hn | hn
  · change n ∈ (values x L).image (fun u ↦ b * u) at hn
    obtain ⟨v, hv, hvEq⟩ := mem_image.mp hn
    obtain ⟨i, hiEq⟩ := mem_values.mp hv
    have hmatch : a * d * startCompleteVertexLabel z L k = c * startCompleteVertexLabel x L i := by
      apply mul_left_cancel₀ hb.ne'
      calc
        b * (a * d * startCompleteVertexLabel z L k) = a * b * d * startCompleteVertexLabel z L k := by ring
        _ = c * n := heq
        _ = b * (c * startCompleteVertexLabel x L i) := by rw [← hvEq, ← hiEq]; ring
    have hcong := one_family_congruence hc hx hz i₀ i k h hbaseX htarget hmatch
    exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hinterval, hcong⟩))
  · change n ∈ (values y L).image (fun u ↦ a * u) at hn
    obtain ⟨v, hv, hvEq⟩ := mem_image.mp hn
    obtain ⟨j, hjEq⟩ := mem_values.mp hv
    have hmatch : b * d * startCompleteVertexLabel z L k = c * startCompleteVertexLabel y L j := by
      apply mul_left_cancel₀ ha.ne'
      calc
        a * (b * d * startCompleteVertexLabel z L k) = a * b * d * startCompleteVertexLabel z L k := by ring
        _ = c * n := heq
        _ = a * (c * startCompleteVertexLabel y L j) := by rw [← hvEq, ← hjEq]; ring
    have hcong := one_family_congruence hc hy hz j₀ j k h hbaseY htarget hmatch
    exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hinterval, hcong⟩))

theorem cardinal_le_classes {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i₀ j₀ : Fin (L + 1)) (h : ℤ)
    (hbaseX : startCompleteVertexLabel x L i₀ = a * t)
    (hbaseY : startCompleteVertexLabel y L j₀ = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h) :
    (exactOffsets a b c d x y z L).card ≤ (matchOffsets a b c d h (-1) L).card := by
  rw [← integerOffsets_card]
  exact card_le_card (integerOffsets_subset ha hb hc hx hy hz i₀ j₀ h hbaseX hbaseY htarget)

theorem nonphysical_match_bound {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i₀ j₀ : Fin (L + 1)) (h : ℤ)
    (hbaseX : startCompleteVertexLabel x L i₀ = a * t)
    (hbaseY : startCompleteVertexLabel y L j₀ = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a)
    (hca : ¬c ∣ a) (hcb : ¬c ∣ b) :
    ((exactOffsets a b c d x y z L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) * FixedChannelGamma.gamma a b + 3 := by
  have hcard := cardinal_le_classes ha (by omega : 0 < b) hc hx hy hz i₀ j₀ h hbaseX hbaseY htarget
  have hcardQ : ((exactOffsets a b c d x y z L).card : ℚ) ≤ (matchOffsets a b c d h (-1) L).card := by
    exact_mod_cast hcard
  exact hcardQ.trans (FixedChannelMatches.window_match_gamma ha hb hab hc hd hcop hlo hhi hca hcb h L)

end PaperP1.ActualNormalizedMatches
