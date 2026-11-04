module

public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Exact finite host counts for all bounded-height geometric channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedGeometricPairCount

open Finset PaperP1.EnlargedPairGeometry

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (M L a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico 2 M) ×ˢ (Ico 2 M)).filter fun xy ↦ Geometric a b xy.1 xy.2 L

def coefficients (B : ℕ) : Finset (ℕ × ℕ) := (Icc 1 (B ^ 3)) ×ˢ (Icc 1 (B ^ 3))

def covered (M L : ℕ) : Finset (ℕ × ℕ) :=
  (coefficients (L + 1)).biUnion fun ab ↦ pairs M L ab.1 ab.2

theorem pairs_card {M L a b : ℕ} (ha : 0 < a) :
    (pairs M L a b).card ≤ M * (2 * ((a + b) * (L + 1)) + 1) := by
  let K := (a + b) * (L + 1)
  let f : ℕ × ℕ → ℕ × ℤ := fun xy ↦ (xy.1, (b : ℤ) * xy.1 - (a : ℤ) * xy.2)
  have hc : (pairs M L a b).card ≤ ((Ico 2 M) ×ˢ Icc (-(K : ℤ)) K).card := by
    apply card_le_card_of_injOn f
    · intro xy hxy
      obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
      have hg' : |(b : ℤ) * xy.1 - (a : ℤ) * xy.2| ≤ (K : ℤ) := by
        simpa only [Geometric, K, Nat.cast_mul] using hg
      exact mem_product.mpr ⟨(mem_product.mp hblock).1, mem_Icc.mpr (abs_le.mp hg')⟩
    · intro xy _hxy uv _huv heq
      have hx := congrArg Prod.fst heq
      have hr := congrArg Prod.snd heq
      change xy.1 = uv.1 at hx
      change (b : ℤ) * xy.1 - (a : ℤ) * xy.2 = (b : ℤ) * uv.1 - (a : ℤ) * uv.2 at hr
      have hp : (a : ℤ) * xy.2 = (a : ℤ) * uv.2 := by rw [hx] at hr; linarith only [hr]
      have hy : xy.2 = uv.2 := by exact_mod_cast mul_left_cancel₀ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) hp
      exact Prod.ext hx hy
  have hK : (Icc (-(K : ℤ)) K).card = 2 * K + 1 := by rw [Int.card_Icc]; omega
  rw [card_product, hK] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (by rw [Nat.card_Ico]; exact Nat.sub_le M 2))

theorem coefficients_card (B : ℕ) : (coefficients B).card = B ^ 6 := by
  have hc : (Icc 1 (B ^ 3)).card = B ^ 3 := by rw [Nat.card_Icc]; omega
  simp only [coefficients, card_product, hc]
  ring

theorem pairs_card_height {M L a b : ℕ} (ha : 0 < a) (haB : a ≤ (L + 1) ^ 3) (hbB : b ≤ (L + 1) ^ 3) :
    (pairs M L a b).card ≤ 5 * M * (L + 1) ^ 4 := by
  have hsum : a + b ≤ 2 * (L + 1) ^ 3 := by omega
  have hm := Nat.mul_le_mul_right (L + 1) hsum
  have hp : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
  have hpos : 1 ≤ (L + 1) ^ 4 := by have h := pow_pos (by omega : 0 < L + 1) 4; omega
  have hK : 2 * ((a + b) * (L + 1)) + 1 ≤ 5 * (L + 1) ^ 4 := by nlinarith only [hm, hp, hpos]
  calc
    _ ≤ M * (2 * ((a + b) * (L + 1)) + 1) := pairs_card ha
    _ ≤ M * (5 * (L + 1) ^ 4) := Nat.mul_le_mul_left M hK
    _ = _ := by ring

theorem covered_card (M L : ℕ) : (covered M L).card ≤ 5 * M * (L + 1) ^ 10 := by
  calc
    _ ≤ ∑ ab ∈ coefficients (L + 1), (pairs M L ab.1 ab.2).card := card_biUnion_le
    _ ≤ ∑ _ab ∈ coefficients (L + 1), 5 * M * (L + 1) ^ 4 := by
      apply sum_le_sum
      intro ab hab
      obtain ⟨ha, hb⟩ := mem_product.mp hab
      obtain ⟨ha1, haB⟩ := mem_Icc.mp ha
      obtain ⟨_hb1, hbB⟩ := mem_Icc.mp hb
      exact pairs_card_height (by omega) haB hbB
    _ = _ := by
      simp only [sum_const, coefficients_card, nsmul_eq_mul, Nat.cast_id]
      ring

end PaperP1.BoundedGeometricPairCount
