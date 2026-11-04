module

public import PaperP1.Analysis.RelativeIntervalAxisBounds

/-! # Literal finite integer counts in moving real intervals and strips -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerRealIntervalCount

open Finset

theorem interval_card (S : Finset ℤ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) : (S.card : ℝ) ≤ b - a + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero]
    linarith
  · have hsub : S ⊆ Icc (S.min' hne) (S.max' hne) := by
      intro n hn
      exact mem_Icc.mpr ⟨S.min'_le n hn, S.le_max' n hn⟩
    have horder := S.min'_le_max' hne
    have hcardZ := Int.card_Icc_of_le (S.min' hne) (S.max' hne) (by omega)
    have hcardR : ((Icc (S.min' hne) (S.max' hne)).card : ℝ) =
        (S.max' hne : ℝ) + 1 - (S.min' hne : ℝ) := by exact_mod_cast hcardZ
    have hlo := (hS _ (S.min'_mem hne)).1
    have hhi := (hS _ (S.max'_mem hne)).2
    calc
      _ ≤ ((Icc (S.min' hne) (S.max' hne)).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = _ := hcardR
      _ ≤ _ := by linarith

theorem band_card (S : Finset ℤ) (center B : ℝ) (hB : 0 ≤ B)
    (hS : ∀ n ∈ S, |(n : ℝ) - center| ≤ B) : (S.card : ℝ) ≤ 2 * B + 1 := by
  have h := interval_card S (center - B) (center + B) (by linarith) (fun n hn ↦ by
    have hb := abs_le.mp (hS n hn)
    constructor <;> linarith)
  convert h using 1
  ring

theorem strip_card (S : Finset (ℤ × ℤ)) (A B R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, |(p.1 : ℝ)| ≤ A ∧ |(p.2 : ℝ) - R * (p.1 : ℝ)| ≤ B) :
    (S.card : ℝ) ≤ (2 * A + 1) * (2 * B + 1) := by
  have hfirst : ((S.image Prod.fst).card : ℝ) ≤ 2 * A + 1 := by
    apply band_card _ 0 A hA
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    simpa only [sub_zero] using (hS p hp).1
  have hsecond (a : ℤ) : ((S.filter (fun p ↦ p.1 = a)).card : ℝ) ≤ 2 * B + 1 := by
    let V := S.filter (fun p ↦ p.1 = a)
    have hinj : V.card ≤ (V.image Prod.snd).card := by
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        exact mem_image_of_mem _ hp
      · intro p hp q hq heq
        exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) heq
    have hband : ((V.image Prod.snd).card : ℝ) ≤ 2 * B + 1 := by
      apply band_card _ (R * (a : ℝ)) B hB
      intro n hn
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
      have h := (hS p (mem_filter.mp hp).1).2
      simpa only [(mem_filter.mp hp).2] using h
    exact (show (V.card : ℝ) ≤ (V.image Prod.snd).card by exact_mod_cast hinj).trans hband
  calc
    _ = ∑ a ∈ S.image Prod.fst, ((S.filter (fun p ↦ p.1 = a)).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image Prod.fst S
    _ ≤ ∑ _a ∈ S.image Prod.fst, (2 * B + 1) := sum_le_sum (fun a _ ↦ hsecond a)
    _ = ((S.image Prod.fst).card : ℝ) * (2 * B + 1) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hfirst (by linarith)

end PaperP1.IntegerRealIntervalCount
