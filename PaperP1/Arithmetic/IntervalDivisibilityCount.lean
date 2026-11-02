module

public import PaperP1.Arithmetic.NormalizedUnitCount
public import Mathlib.Data.Nat.Factorization.Basic

/-! # Uniform counts of one or two divisibility classes in an arbitrary complete window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalDivisibilityCount

open Finset PaperP1.NormalizedWindowSets

def hits (d x L : ℕ) : Finset ℕ := (values x L).filter (d ∣ ·)

theorem values_Ioc {x L : ℕ} (hx : 2 ≤ x) : values x L = Ioc (x - 2) (x + L - 1) := by
  rw [values_eq_interval (by omega : 0 < x)]
  ext n
  simp only [mem_Ico, mem_Ioc]
  omega

theorem count_add_div {x L : ℕ} (hx : 2 ≤ x) (d : ℕ) :
    (hits d x L).card + (x - 2) / d = (x + L - 1) / d := by
  have heq : (Ioc 0 (x + L - 1)).filter (d ∣ ·) = (Ioc 0 (x - 2)).filter (d ∣ ·) ∪ hits d x L := by
    ext n
    simp only [hits, values_Ioc hx, mem_filter, mem_Ioc, mem_union]
    omega
  have hdis : Disjoint ((Ioc 0 (x - 2)).filter (d ∣ ·)) (hits d x L) := by
    apply disjoint_left.mpr
    intro n hn hm
    have hlo := mem_Ioc.mp (mem_filter.mp hn).1
    have hhi := mem_Ioc.mp ((values_Ioc hx).symm ▸ (mem_filter.mp hm).1)
    omega
  have hh := Nat.Ioc_filter_dvd_card_eq_div (x + L - 1) d
  rw [heq, card_union_of_disjoint hdis, Nat.Ioc_filter_dvd_card_eq_div] at hh
  omega

theorem count_bounds {x L d : ℕ} (hx : 2 ≤ x) (hd : 0 < d) :
    ((L + 1 : ℕ) : ℝ) / d - 1 ≤ ((hits d x L).card : ℝ) ∧
      ((hits d x L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / d + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : ((hits d x L).card : ℝ) + ((x - 2) / d : ℕ) = ((x + L - 1) / d : ℕ) := by
    exact_mod_cast count_add_div hx d
  have hm := congrArg (fun z : ℝ ↦ (d : ℝ) * z) hc
  simp only [mul_add] at hm
  have hlo : (d : ℝ) * (((x - 2) / d : ℕ) : ℝ) + ((x - 2) % d : ℕ) = (x - 2 : ℕ) := by
    exact_mod_cast Nat.div_add_mod (x - 2) d
  have hhi : (d : ℝ) * (((x + L - 1) / d : ℕ) : ℝ) + ((x + L - 1) % d : ℕ) = (x + L - 1 : ℕ) := by
    exact_mod_cast Nat.div_add_mod (x + L - 1) d
  have hwidth : ((x + L - 1 : ℕ) : ℝ) = ((x - 2 : ℕ) : ℝ) + ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show x + L - 1 = x - 2 + (L + 1) by omega)
  have hremLo : (((x - 2) % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt (x - 2) hd
  have hremHi : (((x + L - 1) % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt (x + L - 1) hd
  have hLoNon : (0 : ℝ) ≤ ((x - 2) % d : ℕ) := Nat.cast_nonneg _
  have hHiNon : (0 : ℝ) ≤ ((x + L - 1) % d : ℕ) := Nat.cast_nonneg _
  constructor
  · have hh : ((L + 1 : ℕ) : ℝ) / d ≤ ((hits d x L).card : ℝ) + 1 := by
      apply (div_le_iff₀ hdR).mpr
      nlinarith only [hm, hlo, hhi, hwidth, hremHi, hLoNon]
    linarith only [hh]
  · have hh : ((hits d x L).card : ℝ) - 1 ≤ ((L + 1 : ℕ) : ℝ) / d := by
      apply (le_div_iff₀ hdR).mpr
      nlinarith only [hm, hlo, hhi, hwidth, hremLo, hHiNon]
    linarith only [hh]

theorem hits_inter (a b x L : ℕ) : hits a x L ∩ hits b x L = hits (Nat.lcm a b) x L := by
  ext n
  simp only [hits, mem_inter, mem_filter, Nat.lcm_dvd_iff]
  tauto

theorem union_bound {a b x L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) :
    ((hits a x L ∪ hits b x L).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) / a + ((L + 1 : ℕ) : ℝ) / b -
        ((L + 1 : ℕ) : ℝ) / Nat.lcm a b + 3 := by
  have hcard := card_union_add_card_inter (hits a x L) (hits b x L)
  rw [hits_inter] at hcard
  have hcardR : ((hits a x L ∪ hits b x L).card : ℝ) + (hits (Nat.lcm a b) x L).card =
      (hits a x L).card + (hits b x L).card := by exact_mod_cast hcard
  have haB := (count_bounds (L := L) hx ha).2
  have hbB := (count_bounds (L := L) hx hb).2
  have hiB := (count_bounds (L := L) hx (Nat.lcm_pos ha hb)).1
  linarith only [hcardR, haB, hbB, hiB]

end PaperP1.IntervalDivisibilityCount
