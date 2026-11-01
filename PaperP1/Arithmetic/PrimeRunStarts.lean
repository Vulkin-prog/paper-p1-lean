module

public import PaperP1.Combinatorics.IntervalMultiples
public import PaperP1.Arithmetic.ShortIntervalCongruences
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Many dyadic starts qu+1 avoid both exceptional residue classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeRunStarts

open Finset

def parameters (N q : ℕ) : Finset ℕ := Ico (N / q + 1) (N / q + 1 + (N / q - 1))

def goodParameters (N q : ℕ) : Finset ℕ := (parameters N q).filter fun u ↦ ¬q ∣ u ∧ ¬q ∣ u + 1

def starts (N q : ℕ) : Finset ℕ := (goodParameters N q).image fun u ↦ q * u + 1

theorem mem_starts (N q x : ℕ) : x ∈ starts N q ↔
    ∃ u ∈ parameters N q, ¬q ∣ u ∧ ¬q ∣ u + 1 ∧ q * u + 1 = x := by
  simp only [starts, mem_image, goodParameters, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hq, hq1⟩, hx⟩
    exact ⟨u, hu, hq, hq1, hx⟩
  · rintro ⟨u, hu, hq, hq1, hx⟩
    exact ⟨u, ⟨hu, hq, hq1⟩, hx⟩

theorem parameters_card (N q : ℕ) : (parameters N q).card = N / q - 1 := by
  simp only [parameters, Nat.card_Ico, Nat.add_sub_cancel_left]

theorem starts_subset_interval {N q : ℕ} (hq : 2 ≤ q) (hqN : q ≤ N) : starts N q ⊆ Ico N (2 * N) := by
  intro x hx
  obtain ⟨u, hu, _, _, rfl⟩ := (mem_starts N q x).mp hx
  have hqpos : 0 < q := by omega
  have hdiv : 1 ≤ N / q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
  obtain ⟨huLo, huHi⟩ := mem_Ico.mp hu
  have hlo := Nat.mul_le_mul_left q huLo
  have hhi := Nat.mul_le_mul_left q (show u + 1 ≤ 2 * (N / q) by omega)
  have hmod := Nat.mod_add_div N q
  have hmodlt := Nat.mod_lt N hqpos
  have hdivle := Nat.div_mul_le_self N q
  rw [Nat.mul_add, Nat.mul_one] at hlo hhi
  exact mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩

theorem card_parameters_succ_divisible_le (N q : ℕ) :
    ((parameters N q).filter fun u ↦ q ∣ u + 1).card ≤ (N / q - 1) / q + 1 := by
  apply PaperP1.ShortIntervalCongruences.card_common_residue_le _ (N / q + 1) (N / q - 1) q
  · exact filter_subset _ _
  · intro u hu v hv
    have h := Nat.dvd_sub (mem_filter.mp hv).2 (mem_filter.mp hu).2
    simpa only [Nat.add_sub_add_right] using h

theorem goodParameters_card_lower (N q : ℕ) :
    N / q - 1 ≤ (goodParameters N q).card + 2 * ((N / q - 1) / q + 1) := by
  let bad₀ := (parameters N q).filter fun u ↦ q ∣ u
  let bad₁ := (parameters N q).filter fun u ↦ q ∣ u + 1
  have hcover : parameters N q ⊆ (goodParameters N q ∪ bad₀) ∪ bad₁ := by
    intro u hu
    by_cases hq : q ∣ u
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hu, hq⟩))
    · by_cases hq1 : q ∣ u + 1
      · exact mem_union_right _ (mem_filter.mpr ⟨hu, hq1⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hu, hq, hq1⟩))
  have hbad₀ : bad₀.card ≤ (N / q - 1) / q + 1 := PaperP1.IntervalMultiples.card_multiples_interval_le _ _ _
  have hbad₁ : bad₁.card ≤ (N / q - 1) / q + 1 := card_parameters_succ_divisible_le N q
  have hcard := card_le_card hcover
  rw [parameters_card] at hcard
  have hfirst := card_union_le (goodParameters N q) bad₀
  have hsecond := card_union_le (goodParameters N q ∪ bad₀) bad₁
  omega

theorem starts_card (N q : ℕ) (hq : 0 < q) : (starts N q).card = (goodParameters N q).card := by
  apply card_image_of_injective
  intro u v huv
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel huv)

theorem starts_card_lower {N q : ℕ} (hq : 2 ≤ q) (hqN : q ≤ N) :
    (N : ℝ) / q - 2 * N / (q : ℝ) ^ 2 - 4 ≤ (starts N q).card := by
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hdiv : 1 ≤ N / q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
  have hfloorUpper : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have hfloorLower : (N : ℝ) / q - 1 ≤ (N / q : ℕ) := by
    have hmod := Nat.mod_add_div N q
    have hmodlt := Nat.mod_lt N hqpos
    have hidR : ((N % q : ℕ) : ℝ) + (q : ℝ) * ((N / q : ℕ) : ℝ) = N := by exact_mod_cast hmod
    have hltR : ((N % q : ℕ) : ℝ) < q := by exact_mod_cast hmodlt
    have hnext : (N : ℝ) / q ≤ ((N / q : ℕ) : ℝ) + 1 := (div_le_iff₀ hqR).mpr (by nlinarith)
    linarith
  have hlength : ((N / q - 1 : ℕ) : ℝ) = ((N / q : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub hdiv]; norm_num
  have hlengthUpper : ((N / q - 1 : ℕ) : ℝ) ≤ (N : ℝ) / q := by rw [hlength]; linarith
  have hbadFloor : (((N / q - 1) / q : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) ^ 2 := by
    calc
      _ ≤ ((N / q - 1 : ℕ) : ℝ) / q := Nat.cast_div_le
      _ ≤ ((N : ℝ) / q) / q := div_le_div_of_nonneg_right hlengthUpper hqR.le
      _ = _ := by ring
  have hcardNat := goodParameters_card_lower N q
  have hcardR : ((N / q - 1 : ℕ) : ℝ) ≤ ((goodParameters N q).card : ℝ) +
      2 * ((((N / q - 1) / q : ℕ) : ℝ) + 1) := by exact_mod_cast hcardNat
  rw [starts_card N q hqpos]
  rw [hlength] at hcardR
  rw [mul_div_assoc]
  linarith

end PaperP1.PrimeRunStarts
