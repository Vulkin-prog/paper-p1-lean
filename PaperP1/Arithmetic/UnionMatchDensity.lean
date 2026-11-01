module

public import PaperP1.Arithmetic.AffineResidueClasses
public import PaperP1.Arithmetic.ChannelMatchDensity

/-! # The exact finite error for the two fixed-channel matching classes -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.UnionMatchDensity

open Finset PaperP1.AffineResidueClasses PaperP1.ChannelMatchDensity

theorem divisible_lcm_iff {r s c : ℕ} (hrc : r ∣ c) (hsc : s ∣ c) (hlcm : r.lcm s = c) (n : ℤ) :
    (c : ℤ) ∣ n ↔ (r : ℤ) ∣ n ∧ (s : ℤ) ∣ n := by
  constructor
  · intro hn
    exact ⟨(Int.natCast_dvd_natCast.mpr hrc).trans hn, (Int.natCast_dvd_natCast.mpr hsc).trans hn⟩
  · rintro ⟨hr, hs⟩
    apply Int.natCast_dvd.mpr
    rw [← hlcm]
    exact Nat.lcm_dvd (Int.natCast_dvd.mp hr) (Int.natCast_dvd.mp hs)

theorem solutions_intersection {r s c d : ℕ} (hrc : r ∣ c) (hsc : s ∣ c) (hlcm : r.lcm s = c) (h a b : ℤ) :
    solutions c d h a b = solutions r d h a b ∩ solutions s d h a b := by
  ext k
  simp only [solutions, mem_filter, mem_inter]
  constructor
  · rintro ⟨hk, hdiv⟩
    obtain ⟨hr, hs⟩ := (divisible_lcm_iff hrc hsc hlcm _).mp hdiv
    exact ⟨⟨hk, hr⟩, hk, hs⟩
  · rintro ⟨⟨hk, hr⟩, _, hs⟩
    exact ⟨hk, (divisible_lcm_iff hrc hsc hlcm _).mpr ⟨hr, hs⟩⟩

theorem union_abs_error {r s c d : ℕ} (hr : 0 < r) (hs : 0 < s) (hc : 0 < c)
    (hrc : r ∣ c) (hsc : s ∣ c) (hlcm : r.lcm s = c) (hcop : d.Coprime c) (h a b : ℤ) (hab : a ≤ b) :
    |((solutions r d h a b ∪ solutions s d h a b).card : ℚ) -
      ((b - a : ℤ) : ℚ) * (1 / (r : ℚ) + 1 / (s : ℚ) - 1 / (c : ℚ))| ≤ 3 := by
  have herrorR := abs_le.mp (AffineResidueClasses.abs_error hr (hcop.coprime_dvd_right hrc) h a b hab)
  have herrorS := abs_le.mp (AffineResidueClasses.abs_error hs (hcop.coprime_dvd_right hsc) h a b hab)
  have herrorC := abs_le.mp (AffineResidueClasses.abs_error hc hcop h a b hab)
  have hcard := card_union_add_card_inter (solutions r d h a b) (solutions s d h a b)
  rw [← solutions_intersection hrc hsc hlcm] at hcard
  have hcardQ : ((solutions r d h a b ∪ solutions s d h a b).card : ℚ) + (solutions c d h a b).card =
      (solutions r d h a b).card + (solutions s d h a b).card := by exact_mod_cast hcard
  have hcentre : ((b - a : ℤ) : ℚ) * (1 / (r : ℚ) + 1 / (s : ℚ) - 1 / (c : ℚ)) =
      ((b - a : ℤ) : ℚ) / r + ((b - a : ℤ) : ℚ) / s - ((b - a : ℤ) : ℚ) / c := by ring
  rw [hcentre]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gcd_quotient_moduli {a b c : ℕ} (hab : a.Coprime b) (hc : 0 < c) :
    0 < c / c.gcd a ∧ 0 < c / c.gcd b ∧ c / c.gcd a ∣ c ∧ c / c.gcd b ∣ c ∧
      (c / c.gcd a).lcm (c / c.gcd b) = c := by
  have hprodA : c / c.gcd a * c.gcd a = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c a)
  have hprodB : c / c.gcd b * c.gcd b = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c b)
  have hr : 0 < c / c.gcd a := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hprodA
    exact hc.ne' hprodA.symm
  have hs : 0 < c / c.gcd b := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hprodB
    exact hc.ne' hprodB.symm
  refine ⟨hr, hs, ⟨c.gcd a, hprodA.symm⟩, ⟨c.gcd b, hprodB.symm⟩, ?_⟩
  have hcop := hab.gcd_both c c
  change (c.gcd a).gcd (c.gcd b) = 1 at hcop
  have h := Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left c a) (Nat.gcd_dvd_left c b)
  simpa only [hcop, Nat.div_one] using h

theorem reciprocal_of_product {r g c : ℕ} (hr : 0 < r) (hc : 0 < c) (heq : r * g = c) :
    1 / (r : ℚ) = (g : ℚ) / c := by
  apply (div_eq_div_iff (by exact_mod_cast hr.ne' : (r : ℚ) ≠ 0)
    (by exact_mod_cast hc.ne' : (c : ℚ) ≠ 0)).mpr
  have hQ : (r : ℚ) * g = c := by exact_mod_cast heq
  nlinarith

theorem reciprocal_density_identity {a b c : ℕ} (hc : 0 < c) :
    1 / ((c / c.gcd a : ℕ) : ℚ) + 1 / ((c / c.gcd b : ℕ) : ℚ) - 1 / (c : ℚ) = density a b c := by
  have hprodA : c / c.gcd a * c.gcd a = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c a)
  have hprodB : c / c.gcd b * c.gcd b = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c b)
  have hr : 0 < c / c.gcd a := by nlinarith
  have hs : 0 < c / c.gcd b := by nlinarith
  have hg : 0 < c.gcd a := Nat.gcd_pos_of_pos_left a hc
  have hh : 0 < c.gcd b := Nat.gcd_pos_of_pos_left b hc
  have hnum : ((c.gcd a + c.gcd b - 1 : ℕ) : ℚ) = (c.gcd a : ℚ) + c.gcd b - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [reciprocal_of_product hr hc hprodA, reciprocal_of_product hs hc hprodB, density, hnum]
  ring

def matchOffsets (a b c d : ℕ) (h lo hi : ℤ) : Finset ℤ :=
  solutions (c / c.gcd a) d h lo hi ∪ solutions (c / c.gcd b) d h lo hi

theorem abs_match_error {a b c d : ℕ} (hab : a.Coprime b) (hc : 0 < c) (hcop : c.Coprime d)
    (h lo hi : ℤ) (hinterval : lo ≤ hi) :
    |((matchOffsets a b c d h lo hi).card : ℚ) - ((hi - lo : ℤ) : ℚ) * density a b c| ≤ 3 := by
  obtain ⟨hr, hs, hrc, hsc, hlcm⟩ := gcd_quotient_moduli hab hc
  have hbound := union_abs_error hr hs hc hrc hsc hlcm hcop.symm h lo hi hinterval
  rw [reciprocal_density_identity hc] at hbound
  exact hbound

theorem window_match_upper {a b c d : ℕ} (hab : a.Coprime b) (hc : 0 < c) (hcop : c.Coprime d)
    (h : ℤ) (L : ℕ) :
    ((matchOffsets a b c d h (-1) L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) * density a b c + 3 := by
  have hbound := (abs_le.mp (abs_match_error hab hc hcop h (-1) L (by omega))).2
  have hlen : (((L : ℤ) - (-1) : ℤ) : ℚ) = ((L + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hlen] at hbound
  linarith

end PaperP1.UnionMatchDensity
