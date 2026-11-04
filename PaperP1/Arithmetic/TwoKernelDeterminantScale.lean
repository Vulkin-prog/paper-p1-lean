module

public import PaperP1.Arithmetic.TwoKernelDeterminantBoxes

/-! # Occupied determinant boxes preserve the actual coefficient scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoKernelDeterminantScale

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.TwoSmallKernelSquareParts
  PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def occupied (H h c₁ c₂ X : ℕ) (S : Finset ℕ) : Finset Quad :=
  (boxes X).filter fun a ↦ ∃ n ∈ S, canonicalCode H h n ∈
    solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)

theorem finite_cover_occupied {H h c₁ c₂ X : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n + h ≤ X ∧
      smallOddPart H n = c₁ ∧ smallOddPart H (n + h) = c₂) :
    S.card ≤ ∑ a ∈ occupied H h c₁ c₂ X S,
      (solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card := by
  rw [← card_image_of_injOn (canonicalCode_injective S (by
    intro n hn; exact ⟨(hS n hn).1, (hS n hn).2.2.1⟩))]
  calc
    _ ≤ ((occupied H h c₁ c₂ X S).biUnion fun a ↦ solutions c₁ c₂ h
        (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card := by
      apply card_le_card
      intro q hq
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
      obtain ⟨a, ha, hbox⟩ := canonical_in_box (hS n hn).1 (hS n hn).2.1
        (hS n hn).2.2.1 (hS n hn).2.2.2
      exact mem_biUnion.mpr ⟨a, mem_filter.mpr ⟨ha, n, hn, hbox⟩, hbox⟩
    _ ≤ _ := card_biUnion_le

theorem box_product_bounds {c d u D U : ℕ} (hd : d ∈ Ico D (2 * D))
    (hu : u ∈ Ico U (2 * U)) :
    c * D ^ 2 * U ≤ c * d ^ 2 * u ∧ c * d ^ 2 * u ≤ 8 * (c * D ^ 2 * U) := by
  obtain ⟨hdlo, hdhi⟩ := mem_Ico.mp hd
  obtain ⟨hulo, huhi⟩ := mem_Ico.mp hu
  constructor
  · exact Nat.mul_le_mul (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hdlo 2)) hulo
  · calc
      _ ≤ c * (2 * D) ^ 2 * (2 * U) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hdhi.le 2)) huhi.le
      _ = _ := by ring

theorem canonical_box_bounds {H h n c₁ c₂ D E U V : ℕ} (hn : 0 < n)
    (hc₁ : smallOddPart H n = c₁) (hc₂ : smallOddPart H (n + h) = c₂)
    (hbox : canonicalCode H h n ∈ solutions c₁ c₂ h D E U V) :
    c₁ * D ^ 2 * U ≤ n ∧ n ≤ 8 * (c₁ * D ^ 2 * U) ∧
      c₂ * E ^ 2 * V ≤ n + h ∧ n + h ≤ 8 * (c₂ * E ^ 2 * V) ∧
        D ^ 2 ≤ n ∧ E ^ 2 ≤ n + h ∧ U ≤ largeOddKernel H n ∧ V ≤ largeOddKernel H (n + h) := by
  obtain ⟨hprod, _⟩ := mem_filter.mp hbox
  obtain ⟨hde, huv⟩ := mem_product.mp hprod
  obtain ⟨hd, he⟩ := mem_product.mp hde
  obtain ⟨hu, hv⟩ := mem_product.mp huv
  have h₁ := decomposition H n hn
  have hm : 0 < n + h := by omega
  have h₂ := decomposition H (n + h) hm
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  have hb₁ := box_product_bounds (c := c₁) hd hu
  have hb₂ := box_product_bounds (c := c₂) he hv
  change c₁ * D ^ 2 * U ≤ c₁ * canonicalSquarePart n ^ 2 * largeOddKernel H n ∧
    c₁ * canonicalSquarePart n ^ 2 * largeOddKernel H n ≤ 8 * (c₁ * D ^ 2 * U) at hb₁
  change c₂ * E ^ 2 * V ≤ c₂ * canonicalSquarePart (n + h) ^ 2 * largeOddKernel H (n + h) ∧
    c₂ * canonicalSquarePart (n + h) ^ 2 * largeOddKernel H (n + h) ≤ 8 * (c₂ * E ^ 2 * V) at hb₂
  rw [h₁] at hb₁
  rw [h₂] at hb₂
  refine ⟨hb₁.1, hb₁.2, hb₂.1, hb₂.2, ?_, ?_, (mem_Ico.mp hu).1, (mem_Ico.mp hv).1⟩
  · exact (Nat.pow_le_pow_left (mem_Ico.mp hd).1 2).trans
      ((Nat.le_mul_of_pos_left _ (largeOddKernel_pos H n)).trans (KernelSquareBudget.kernel_square_le H n hn))
  · exact (Nat.pow_le_pow_left (mem_Ico.mp he).1 2).trans
      ((Nat.le_mul_of_pos_left _ (largeOddKernel_pos H (n + h))).trans (KernelSquareBudget.kernel_square_le H (n + h) hm))

end PaperP1.TwoKernelDeterminantScale
