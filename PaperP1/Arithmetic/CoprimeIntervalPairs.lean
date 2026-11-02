module

public import PaperP1.Arithmetic.IntervalDivisibilityCount
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.FieldSimp

/-! # An explicit elementary supply of coprime pairs in a fixed-ratio interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoprimeIntervalPairs

open Finset

def pairs (M : ℕ) : Finset (ℕ × ℕ) := ((Ioc 0 M) ×ˢ (Ioc 0 M)).filter fun p ↦ p.1.Coprime p.2
def badPairs (M : ℕ) : Finset (ℕ × ℕ) := ((Ioc 0 M) ×ˢ (Ioc 0 M)).filter fun p ↦ ¬p.1.Coprime p.2
def multiples (M d : ℕ) : Finset ℕ := (Ioc 0 M).filter (d ∣ ·)
def intervalPairs (D : ℕ) : Finset (ℕ × ℕ) := (pairs (10 * D)).filter fun p ↦ D ≤ p.1 ∧ D ≤ p.2

theorem reciprocal_square_sum_le (M : ℕ) : (∑ d ∈ Icc 2 M, 1 / (d : ℝ) ^ 2) ≤ 3 / 4 := by
  have hstep (m : ℝ) (hm : 1 ≤ m) : 1 / (m + 1) ^ 2 ≤ 1 / m - 1 / (m + 1) := by
    calc
      _ ≤ 1 / (m * (m + 1)) := one_div_le_one_div_of_le (by positivity) (by nlinarith only [hm])
      _ = _ := by field_simp; ring
  have hstrong (k : ℕ) : (∑ d ∈ Icc 2 (k + 2), 1 / (d : ℝ) ^ 2) ≤ 3 / 4 - 1 / ((k + 2 : ℕ) : ℝ) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega, sum_Icc_succ_top (by omega)]
      have hh := add_le_add ih (hstep ((k + 2 : ℕ) : ℝ) (by exact_mod_cast (show 1 ≤ k + 2 by omega)))
      push_cast at hh ⊢
      linarith only [hh]
  by_cases hM : 2 ≤ M
  · have hh := hstrong (M - 2)
    rw [Nat.sub_add_cancel hM] at hh
    exact hh.trans (sub_le_self _ (by positivity))
  · have hM' : M = 0 ∨ M = 1 := by omega
    rcases hM' with rfl | rfl <;> norm_num

theorem bad_cover (M : ℕ) : badPairs M ⊆
    (Icc 2 M).biUnion fun d ↦ multiples M d ×ˢ multiples M d := by
  intro p hp
  obtain ⟨hbox, hbad⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hbox
  have hxpos := (mem_Ioc.mp hx).1
  have hgpos := Nat.gcd_pos_of_pos_left p.2 hxpos
  have hgne : Nat.gcd p.1 p.2 ≠ 1 := hbad
  have hgM := (Nat.gcd_le_left p.2 hxpos).trans (mem_Ioc.mp hx).2
  exact mem_biUnion.mpr ⟨Nat.gcd p.1 p.2, mem_Icc.mpr ⟨by omega, hgM⟩,
    mem_product.mpr ⟨mem_filter.mpr ⟨hx, Nat.gcd_dvd_left _ _⟩, mem_filter.mpr ⟨hy, Nat.gcd_dvd_right _ _⟩⟩⟩

theorem bad_card (M : ℕ) : ((badPairs M).card : ℝ) ≤ (3 / 4 : ℝ) * (M : ℝ) ^ 2 := by
  have hcard : (badPairs M).card ≤ ∑ d ∈ Icc 2 M, (M / d) ^ 2 := by
    have hh := (card_le_card (bad_cover M)).trans card_biUnion_le
    simpa only [card_product, multiples, Nat.Ioc_filter_dvd_card_eq_div, pow_two] using hh
  calc
    _ ≤ ∑ d ∈ Icc 2 M, (((M / d : ℕ) : ℝ) ^ 2) := by exact_mod_cast hcard
    _ ≤ ∑ d ∈ Icc 2 M, (M : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
      apply sum_le_sum
      intro d hd
      calc
        _ ≤ ((M : ℝ) / d) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) Nat.cast_div_le 2
        _ = _ := by rw [div_pow]; ring
    _ = (M : ℝ) ^ 2 * (∑ d ∈ Icc 2 M, 1 / (d : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ (M : ℝ) ^ 2 * (3 / 4) := mul_le_mul_of_nonneg_left (reciprocal_square_sum_le M) (sq_nonneg _)
    _ = _ := by ring

theorem pairs_card_lower (M : ℕ) : (M : ℝ) ^ 2 / 4 ≤ ((pairs M).card : ℝ) := by
  have hsplit : ((pairs M).card : ℝ) + (badPairs M).card = (M : ℝ) ^ 2 := by
    have hh := card_filter_add_card_filter_not (s := (Ioc 0 M) ×ˢ (Ioc 0 M)) (fun p ↦ p.1.Coprime p.2)
    simpa only [pairs, badPairs, card_product, Nat.card_Ioc, Nat.sub_zero, Nat.cast_mul, pow_two, Nat.cast_add] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) hh
  have hbad := bad_card M
  linarith only [hsplit, hbad]

theorem intervalPairs_data {D : ℕ} {p : ℕ × ℕ} (hp : p ∈ intervalPairs D) :
    0 < p.1 ∧ 0 < p.2 ∧ D ≤ p.1 ∧ p.1 ≤ 10 * D ∧ D ≤ p.2 ∧ p.2 ≤ 10 * D ∧ p.1.Coprime p.2 := by
  obtain ⟨hpair, hlo⟩ := mem_filter.mp hp
  obtain ⟨hbox, hcop⟩ := mem_filter.mp hpair
  obtain ⟨hx, hy⟩ := mem_product.mp hbox
  exact ⟨(mem_Ioc.mp hx).1, (mem_Ioc.mp hy).1, hlo.1, (mem_Ioc.mp hx).2, hlo.2, (mem_Ioc.mp hy).2, hcop⟩

theorem intervalPairs_card_lower (D : ℕ) : 5 * (D : ℝ) ^ 2 ≤ ((intervalPairs D).card : ℝ) := by
  have hcover : pairs (10 * D) ⊆
      (intervalPairs D ∪ ((Ioc 0 D) ×ˢ (Ioc 0 (10 * D)))) ∪ ((Ioc 0 (10 * D)) ×ˢ (Ioc 0 D)) := by
    intro p hp
    have hbox := (mem_filter.mp hp).1
    obtain ⟨hx, hy⟩ := mem_product.mp hbox
    by_cases hxD : D ≤ p.1
    · by_cases hyD : D ≤ p.2
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp, hxD, hyD⟩))
      · exact mem_union_right _ (mem_product.mpr ⟨hx, mem_Ioc.mpr ⟨(mem_Ioc.mp hy).1, by omega⟩⟩)
    · exact mem_union_left _ (mem_union_right _
        (mem_product.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hx).1, by omega⟩, hy⟩))
  have hcard : (pairs (10 * D)).card ≤ (intervalPairs D).card + D * (10 * D) + (10 * D) * D := by
    have houter := card_union_le (s := intervalPairs D ∪ ((Ioc 0 D) ×ˢ (Ioc 0 (10 * D))))
      (t := (Ioc 0 (10 * D)) ×ˢ (Ioc 0 D))
    have hinner := card_union_le (s := intervalPairs D) (t := (Ioc 0 D) ×ˢ (Ioc 0 (10 * D)))
    have hh := (card_le_card hcover).trans (houter.trans (Nat.add_le_add_right hinner _))
    simpa only [card_product, Nat.card_Ioc, Nat.sub_zero] using hh
  have hcardR : ((pairs (10 * D)).card : ℝ) ≤ (intervalPairs D).card + 20 * (D : ℝ) ^ 2 := by
    have hh : ((pairs (10 * D)).card : ℝ) ≤
        (intervalPairs D).card + (D : ℝ) * (10 * D) + (10 * D) * D := by exact_mod_cast hcard
    nlinarith only [hh]
  have hlow := pairs_card_lower (10 * D)
  push_cast at hlow
  nlinarith only [hlow, hcardR]

end PaperP1.CoprimeIntervalPairs
