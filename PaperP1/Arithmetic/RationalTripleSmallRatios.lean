module

public import PaperP1.Arithmetic.RationalTripleDensity
public import Mathlib.Tactic.FieldSimp

/-! # Exact small-ratio cases and the gap below the extremal triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleSmallRatios

open PaperP1.RationalTripleDensity

theorem scaled_third_bound {a b c d : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hd : 0 < d) (hc : 0 < c) (hcop : Nat.Coprime a b) (hcd : Nat.Coprime c d) :
    density (a * d) (b * d) c ≤ 1 / (b : ℝ) +
      ((Nat.gcd c a : ℝ) + Nat.gcd c b - 1) / c := by
  have hgeom := third_window_bound (Nat.mul_pos ha hd) (Nat.mul_le_mul_right d hab) hc
  have hgcd : Nat.gcd (a * d) (b * d) = d := by
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, Nat.one_mul]
  have hca : Nat.gcd (a * d) c = Nat.gcd c a := by
    rw [Nat.gcd_comm, Nat.gcd_mul_left_right_of_gcd_eq_one hcd.gcd_eq_one]
  have hcb : Nat.gcd (b * d) c = Nat.gcd c b := by
    rw [Nat.gcd_comm, Nat.gcd_mul_left_right_of_gcd_eq_one hcd.gcd_eq_one]
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hratio : (d : ℝ) / (b * d : ℕ) = 1 / (b : ℝ) := by
    rw [Nat.cast_mul]
    field_simp
  rw [hgcd, hca, hcb, hratio] at hgeom
  exact hgeom

theorem numerator23 (c : ℕ) :
    ((Nat.gcd c 2 : ℝ) + Nat.gcd c 3 - 1) ≤ (c : ℝ) / 4 ∨
      c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 ∨ c = 9 ∨ c = 12 := by
  by_cases hc : 16 ≤ c
  · left
    have h2 : (Nat.gcd c 2 : ℝ) ≤ 2 := by exact_mod_cast Nat.gcd_le_right c (by norm_num : 0 < 2)
    have h3 : (Nat.gcd c 3 : ℝ) ≤ 3 := by exact_mod_cast Nat.gcd_le_right c (by norm_num : 0 < 3)
    have hcR : (16 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  · have hc' : c ≤ 15 := by omega
    interval_cases c <;> norm_num

theorem numerator34 (c : ℕ) :
    ((Nat.gcd c 3 : ℝ) + Nat.gcd c 4 - 1) ≤ (c : ℝ) / 3 ∨
      c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 ∨ c = 8 ∨ c = 12 := by
  by_cases hc : 18 ≤ c
  · left
    have h3 : (Nat.gcd c 3 : ℝ) ≤ 3 := by exact_mod_cast Nat.gcd_le_right c (by norm_num : 0 < 3)
    have h4 : (Nat.gcd c 4 : ℝ) ≤ 4 := by exact_mod_cast Nat.gcd_le_right c (by norm_num : 0 < 4)
    have hcR : (18 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  · have hc' : c ≤ 17 := by omega
    interval_cases c <;> norm_num

/-- The only 2:3 case above 11/18 is the primitive extremal set {10,12,15}. -/
theorem ratio23_gap {c d : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hcd : Nat.Coprime c d) (hlow : 3 * d < 2 * c) (hhigh : c < 4 * d)
    (hne2 : c ≠ 2 * d) (hne3 : c ≠ 3 * d) :
    (d = 5 ∧ c = 12) ∨ density (2 * d) (3 * d) c ≤ 11 / 18 := by
  rcases numerator23 c with hnum | hsmall
  · right
    have hgeom := scaled_third_bound (a := 2) (b := 3) (by norm_num) (by norm_num)
      hd hc (by norm_num [Nat.Coprime]) hcd
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hquarter : ((c : ℝ) / 4) / c = 1 / 4 := by field_simp
    have hquot : ((Nat.gcd c 2 : ℝ) + Nat.gcd c 3 - 1) / c ≤ 1 / 4 := by
      exact (div_le_div_of_nonneg_right hnum hcR.le).trans hquarter.le
    norm_num only [Nat.cast_ofNat] at hgeom
    linarith
  · have hc12 : c ≤ 12 := by omega
    have hd7 : d ≤ 7 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      interval_cases d <;> norm_num [density, pairDensity] <;> omega

theorem ratio34_gap {c d : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hcd : Nat.Coprime c d) (hlow : 2 * d < c) (hhigh : c < 6 * d)
    (hne3 : c ≠ 3 * d) (hne4 : c ≠ 4 * d) :
    density (3 * d) (4 * d) c ≤ 11 / 18 := by
  rcases numerator34 c with hnum | hsmall
  · have hgeom := scaled_third_bound (a := 3) (b := 4) (by norm_num) (by norm_num)
      hd hc (by norm_num [Nat.Coprime]) hcd
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hthird : ((c : ℝ) / 3) / c = 1 / 3 := by field_simp
    have hquot : ((Nat.gcd c 3 : ℝ) + Nat.gcd c 4 - 1) / c ≤ 1 / 3 :=
      (div_le_div_of_nonneg_right hnum hcR.le).trans hthird.le
    norm_num only [Nat.cast_ofNat] at hgeom
    linarith
  · have hc12 : c ≤ 12 := by omega
    have hd5 : d ≤ 5 := by omega
    rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      interval_cases d <;> norm_num [density, pairDensity] <;> omega

end PaperP1.RationalTripleSmallRatios
