module

public import PaperP1.Arithmetic.FixedChannelSourceGeometry

/-! # A fixed rational channel has only O(N(L+1)) actual source pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelLinearCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.FixedChannelSourceGeometry

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem unit_alignment {N a b L : ℕ} (hN : 0 < N) {xy : ℕ × ℕ}
    (hxy : xy ∈ unitSources N a b L) :
    |(b : ℤ) * xy.1 - (a : ℤ) * xy.2| ≤ ((a + b) * (L + 1) : ℕ) := by
  obtain ⟨hblock, u, hu⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  have hunit := congrArg (fun n : ℕ ↦ (n : ℤ)) (mem_units.mp hu)
  push_cast at hunit
  rw [label_cast (hN.trans_le (mem_Ico.mp hx).1),
    label_cast (hN.trans_le (mem_Ico.mp hy).1)] at hunit
  have hu₁ : -((L + 1 : ℕ) : ℤ) ≤ offset u.1 ∧ offset u.1 ≤ ((L + 1 : ℕ) : ℤ) := by
    dsimp [offset]; have h := u.1.isLt; omega
  have hu₂ : -((L + 1 : ℕ) : ℤ) ≤ offset u.2 ∧ offset u.2 ≤ ((L + 1 : ℕ) : ℤ) := by
    dsimp [offset]; have h := u.2.isLt; omega
  have hb₁ := mul_le_mul_of_nonneg_left hu₁.1 (Int.natCast_nonneg b)
  have hb₂ := mul_le_mul_of_nonneg_left hu₁.2 (Int.natCast_nonneg b)
  have ha₁ := mul_le_mul_of_nonneg_left hu₂.1 (Int.natCast_nonneg a)
  have ha₂ := mul_le_mul_of_nonneg_left hu₂.2 (Int.natCast_nonneg a)
  push_cast at hb₁ hb₂ ha₁ ha₂
  push_cast
  exact abs_le.mpr ⟨by nlinarith only [hunit, hb₂, ha₁], by nlinarith only [hunit, hb₁, ha₂]⟩

theorem unit_sources_card_linear {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (unitSources N a b L).card ≤ (2 * (a + b) + 1) * (L + 1) * N := by
  let K := (a + b) * (L + 1)
  let f : ℕ × ℕ → ℕ × ℤ := fun xy ↦ (xy.1, (b : ℤ) * xy.1 - (a : ℤ) * xy.2)
  have hcard : (unitSources N a b L).card ≤
      ((dyadicBlock N) ×ˢ Icc (-(K : ℤ)) K).card := by
    apply card_le_card_of_injOn f
    · intro xy hxy
      have hx := (mem_product.mp (mem_filter.mp hxy).1).1
      exact mem_product.mpr ⟨hx, mem_Icc.mpr (abs_le.mp (unit_alignment hN hxy))⟩
    · intro xy _ uv _ heq
      have hx := congrArg Prod.fst heq
      have he := congrArg Prod.snd heq
      change xy.1 = uv.1 at hx
      change (b : ℤ) * xy.1 - (a : ℤ) * xy.2 = (b : ℤ) * uv.1 - (a : ℤ) * uv.2 at he
      have hy : xy.2 = uv.2 := by
        have hm : (a : ℤ) * xy.2 = (a : ℤ) * uv.2 := by rw [hx] at he; linarith only [he]
        exact_mod_cast (mul_left_cancel₀ (by exact_mod_cast ha.ne' : (a : ℤ) ≠ 0) hm)
      exact Prod.ext hx hy
  have hNc : (dyadicBlock N).card = N := by unfold dyadicBlock; rw [Nat.card_Ico]; omega
  have hKc : (Icc (-(K : ℤ)) K).card = 2 * K + 1 := by
    rw [Int.card_Icc]
    omega
  rw [card_product, hNc, hKc] at hcard
  exact hcard.trans (by dsimp [K]; nlinarith only [show 1 ≤ L + 1 by omega])

end PaperP1.FixedChannelLinearCount
