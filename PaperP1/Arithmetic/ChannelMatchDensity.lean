module

public import PaperP1.Arithmetic.ChannelGeometry
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-! # The coprime-divisor bound behind fixed-channel matching densities -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ChannelMatchDensity

def density (a b c : ℕ) : ℚ := ((c.gcd a + c.gcd b - 1 : ℕ) : ℚ) / c

theorem twice_proper_divisor {g c : ℕ} (hgc : g ∣ c) (hlt : g < c) : 2 * g ≤ c := by
  obtain ⟨k, rfl⟩ := hgc
  have hk : 2 ≤ k := by nlinarith
  nlinarith

theorem three_sum_le_two_product {g h : ℕ} (hg : 2 ≤ g) (hh : 3 ≤ h) :
    3 * (g + h) ≤ 2 * (g * h) + 3 := by
  have hgQ : (2 : ℚ) ≤ g := by exact_mod_cast hg
  have hhQ : (3 : ℚ) ≤ h := by exact_mod_cast hh
  have hprod : (0 : ℚ) ≤ ((g : ℚ) - 2) * ((h : ℚ) - 3) :=
    mul_nonneg (by linarith) (by linarith)
  have hQ : 3 * ((g : ℚ) + h) ≤ 2 * ((g : ℚ) * h) + 3 := by
    nlinarith
  exact_mod_cast hQ

theorem coprime_divisor_bound {g h c : ℕ} (hg : 0 < g) (hh : 0 < h)
    (hcop : g.Coprime h) (hgc : g ∣ c) (hhc : h ∣ c) (hglt : g < c) (hhlt : h < c) :
    3 * (g + h - 1) ≤ 2 * c := by
  by_cases hg1 : g = 1
  · subst g
    have h2 := twice_proper_divisor hhc hhlt
    omega
  by_cases hh1 : h = 1
  · subst h
    have h2 := twice_proper_divisor hgc hglt
    omega
  have hg2 : 2 ≤ g := by omega
  have hh2 : 2 ≤ h := by omega
  have hproduct : g * h ≤ c := Nat.le_of_dvd (by omega) (hcop.mul_dvd_of_dvd_of_dvd hgc hhc)
  have hsum : 3 * (g + h) ≤ 2 * (g * h) + 3 := by
    by_cases hg3 : 3 ≤ g
    · simpa only [add_comm h g, mul_comm h g] using three_sum_le_two_product hh2 hg3
    · have hg_eq : g = 2 := by omega
      have hh3 : 3 ≤ h := by
        by_contra hnot
        have hh_eq : h = 2 := by omega
        norm_num [hg_eq, hh_eq] at hcop
      exact three_sum_le_two_product hg2 hh3
  omega

theorem density_le_two_thirds {a b c : ℕ} (hab : a.Coprime b) (hc : 0 < c)
    (hca : ¬c ∣ a) (hcb : ¬c ∣ b) : density a b c ≤ 2 / 3 := by
  have hg : 0 < c.gcd a := Nat.gcd_pos_of_pos_left a hc
  have hh : 0 < c.gcd b := Nat.gcd_pos_of_pos_left b hc
  have hgc := Nat.gcd_dvd_left c a
  have hhc := Nat.gcd_dvd_left c b
  have hglt : c.gcd a < c := by
    have hle := Nat.le_of_dvd hc hgc
    have hne : c.gcd a ≠ c := by intro h; exact hca (h ▸ Nat.gcd_dvd_right c a)
    omega
  have hhlt : c.gcd b < c := by
    have hle := Nat.le_of_dvd hc hhc
    have hne : c.gcd b ≠ c := by intro h; exact hcb (h ▸ Nat.gcd_dvd_right c b)
    omega
  have hbound := coprime_divisor_bound hg hh (hab.gcd_both c c) hgc hhc hglt hhlt
  have hQ : 3 * ((c.gcd a + c.gcd b - 1 : ℕ) : ℚ) ≤ 2 * (c : ℚ) := by exact_mod_cast hbound
  unfold density
  apply (div_le_iff₀ (by exact_mod_cast hc : (0 : ℚ) < c)).mpr
  nlinarith

end PaperP1.ChannelMatchDensity
