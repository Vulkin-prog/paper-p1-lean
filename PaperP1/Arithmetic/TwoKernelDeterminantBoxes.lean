module

public import PaperP1.Arithmetic.TwoSmallKernelSquareParts
public import Mathlib.Data.Nat.Log

/-! # Actual canonical kernel data lie in literal determinant boxes

The smooth coefficients remain fixed separately. No estimate for the
number of solutions of the determinant equation is assumed or proved here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoKernelDeterminantBoxes

open Finset PaperP1.TwoSmallKernelSquareParts PaperP1.SmallPrimeBudget
  PaperP1.LargeOddKernel PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Quad := (ℕ × ℕ) × (ℕ × ℕ)

def indices (X : ℕ) : Finset ℕ := range (Nat.log 2 X + 1)

def boxes (X : ℕ) : Finset Quad := (indices X ×ˢ indices X) ×ˢ (indices X ×ˢ indices X)

def solutions (c₁ c₂ h D E U V : ℕ) : Finset Quad :=
  (((Ico D (2 * D)) ×ˢ (Ico E (2 * E))) ×ˢ ((Ico U (2 * U)) ×ˢ (Ico V (2 * V)))).filter
    (fun q ↦ c₁ * q.1.1 ^ 2 * q.2.1 + h = c₂ * q.1.2 ^ 2 * q.2.2)

def canonicalCode (H h n : ℕ) : Quad :=
  ((canonicalSquarePart n, canonicalSquarePart (n + h)),
    (largeOddKernel H n, largeOddKernel H (n + h)))

theorem dyadic_cover {n X : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    ∃ a ∈ indices X, n ∈ Ico (2 ^ a) (2 * 2 ^ a) := by
  refine ⟨Nat.log 2 n, mem_range.mpr (by have := Nat.log_mono_right (b := 2) hnX; omega), ?_⟩
  refine mem_Ico.mpr ⟨Nat.pow_log_le_self 2 hn.ne', ?_⟩
  have hh := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  simpa only [pow_succ, mul_comm] using hh

theorem boxes_card (X : ℕ) : (boxes X).card = (Nat.log 2 X + 1) ^ 4 := by
  simp only [boxes, card_product, indices, card_range]
  ring

theorem kernel_le_value (H n : ℕ) (hn : 0 < n) : largeOddKernel H n ≤ n := by
  have hp : 0 < smallOddPart H n * canonicalSquarePart n ^ 2 :=
    mul_pos (smallOddPart_pos H n)
      (pow_pos (Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero n hn.ne')) _)
  have hh := Nat.le_mul_of_pos_left (largeOddKernel H n) hp
  rwa [decomposition H n hn] at hh

theorem canonical_equation {H h n c₁ c₂ : ℕ} (hn : 0 < n)
    (hc₁ : smallOddPart H n = c₁) (hc₂ : smallOddPart H (n + h) = c₂) :
    c₁ * (canonicalCode H h n).1.1 ^ 2 * (canonicalCode H h n).2.1 + h =
      c₂ * (canonicalCode H h n).1.2 ^ 2 * (canonicalCode H h n).2.2 := by
  have h₁ := decomposition H n hn
  have h₂ := decomposition H (n + h) (by omega)
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  change c₁ * canonicalSquarePart n ^ 2 * largeOddKernel H n + h =
    c₂ * canonicalSquarePart (n + h) ^ 2 * largeOddKernel H (n + h)
  rw [h₁, h₂]

theorem canonicalCode_injective {H h c₁ : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ smallOddPart H n = c₁) :
    Set.InjOn (canonicalCode H h) (↑S : Set ℕ) := by
  intro n hn m hm he
  have h₁ := decomposition H n (hS n hn).1
  have h₂ := decomposition H m (hS m hm).1
  rw [(hS n hn).2] at h₁
  rw [(hS m hm).2] at h₂
  have hd := congrArg (fun q : Quad ↦ q.1.1) he
  have hu := congrArg (fun q : Quad ↦ q.2.1) he
  change canonicalSquarePart n = canonicalSquarePart m at hd
  change largeOddKernel H n = largeOddKernel H m at hu
  rw [hd, hu] at h₁
  exact h₁.symm.trans h₂

theorem canonical_in_box {H h n c₁ c₂ X : ℕ} (hn : 0 < n) (hmX : n + h ≤ X)
    (hc₁ : smallOddPart H n = c₁) (hc₂ : smallOddPart H (n + h) = c₂) :
    ∃ a ∈ boxes X, canonicalCode H h n ∈
      solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2) := by
  have hm : 0 < n + h := by omega
  have hnX : n ≤ X := by omega
  obtain ⟨a, ha, hd⟩ := dyadic_cover
    (Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero n hn.ne'))
    ((square_part_le n hn).trans hnX)
  obtain ⟨b, hb, he⟩ := dyadic_cover
    (Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero (n + h) hm.ne'))
    ((square_part_le (n + h) hm).trans hmX)
  obtain ⟨c, hc, hu⟩ := dyadic_cover (largeOddKernel_pos H n) ((kernel_le_value H n hn).trans hnX)
  obtain ⟨d, hd', hv⟩ := dyadic_cover (largeOddKernel_pos H (n + h)) ((kernel_le_value H (n + h) hm).trans hmX)
  refine ⟨((a, b), (c, d)), mem_product.mpr ⟨mem_product.mpr ⟨ha, hb⟩, mem_product.mpr ⟨hc, hd'⟩⟩, ?_⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hd, he⟩, mem_product.mpr ⟨hu, hv⟩⟩,
    canonical_equation hn hc₁ hc₂⟩

theorem finite_cover {H h c₁ c₂ X : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n + h ≤ X ∧
      smallOddPart H n = c₁ ∧ smallOddPart H (n + h) = c₂) :
    S.card ≤ ∑ a ∈ boxes X,
      (solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card := by
  rw [← card_image_of_injOn (canonicalCode_injective S (by
    intro n hn; exact ⟨(hS n hn).1, (hS n hn).2.2.1⟩))]
  calc
    _ ≤ ((boxes X).biUnion fun a ↦ solutions c₁ c₂ h
        (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card := by
      apply card_le_card
      intro q hq
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
      obtain ⟨a, ha, hbox⟩ := canonical_in_box (hS n hn).1 (hS n hn).2.1
        (hS n hn).2.2.1 (hS n hn).2.2.2
      exact mem_biUnion.mpr ⟨a, ha, hbox⟩
    _ ≤ _ := card_biUnion_le

end PaperP1.TwoKernelDeterminantBoxes
