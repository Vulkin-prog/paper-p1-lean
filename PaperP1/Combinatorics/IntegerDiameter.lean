module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Counting finite integer images from their real diameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerDiameter

open Finset

theorem card_le (S : Finset ℤ) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |((a - b : ℤ) : ℝ)| ≤ D) : (S.card : ℝ) ≤ D + 1 := by
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := S.min'_mem hS
    have hb : b ∈ S := S.max'_mem hS
    have hab : a ≤ b := S.min'_le b hb
    have hsub : S ⊆ Icc a b := fun x hx ↦ mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hcardZ : ((Icc a b).card : ℤ) = b - a + 1 := by
      rw [Int.card_Icc]
      omega
    have hcardR : ((Icc a b).card : ℝ) = (b : ℝ) - a + 1 := by exact_mod_cast hcardZ
    have hwidth : (b : ℝ) - a ≤ D := by
      have hh := hdiam b hb a ha
      have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa only [Int.cast_sub, abs_of_nonneg (sub_nonneg.mpr habR)] using hh
    calc
      _ ≤ ((Icc a b).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (b : ℝ) - a + 1 := hcardR
      _ ≤ _ := by linarith only [hwidth]
  · rw [not_nonempty_iff_eq_empty.mp hS, card_empty, Nat.cast_zero]
    linarith only [hD]

theorem image_card_le {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℤ) (D : ℝ)
    (hD : 0 ≤ D) (hinj : Set.InjOn f S)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |((f a - f b : ℤ) : ℝ)| ≤ D) : (S.card : ℝ) ≤ D + 1 := by
  rw [← card_image_iff.mpr hinj]
  apply card_le (S.image f) D hD
  intro a ha b hb
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
  exact hdiam u hu v hv

end PaperP1.IntegerDiameter
