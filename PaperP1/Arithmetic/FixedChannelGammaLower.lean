module

public import PaperP1.Arithmetic.FixedChannelGamma
public import Mathlib.Data.Nat.Prime.Basic

/-! # Every admissible fixed-channel coefficient is at least one third

The candidates `(3a,2)` for odd `a` and `(3b,4)` for odd `b` suffice.
Consequently the printed minimum with `17/24` in T2.7 is redundant.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.FixedChannelGammaLower

open PaperP1.FixedChannelGamma PaperP1.ChannelMatchDensity

theorem density_lower_left {a b : ℕ} (ha : 0 < a) :
    (1 / 3 : ℚ) ≤ density a b (3 * a) := by
  have hg : (3 * a).gcd a = a := by simp
  have hh : 0 < (3 * a).gcd b := Nat.gcd_pos_of_pos_left b (by omega)
  have hcount : a ≤ (3 * a).gcd a + (3 * a).gcd b - 1 := by omega
  have hcast : (a : ℚ) ≤ ((3 * a).gcd a + (3 * a).gcd b - 1 : ℕ) := by exact_mod_cast hcount
  unfold density
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < (3 * a : ℕ))).mpr
  push_cast
  linarith only [hcast]

theorem density_lower_right {a b : ℕ} (hb : 0 < b) :
    (1 / 3 : ℚ) ≤ density a b (3 * b) := by
  have hg : (3 * b).gcd b = b := by simp
  have hh : 0 < (3 * b).gcd a := Nat.gcd_pos_of_pos_left a (by omega)
  have hcount : b ≤ (3 * b).gcd a + (3 * b).gcd b - 1 := by omega
  have hcast : (b : ℚ) ≤ ((3 * b).gcd a + (3 * b).gcd b - 1 : ℕ) := by exact_mod_cast hcount
  unfold density
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < (3 * b : ℕ))).mpr
  push_cast
  linarith only [hcast]

theorem gamma_ge_one_third {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hb2a : b < 2 * a) (hcop : a.Coprime b) : (1 / 3 : ℚ) ≤ gamma a b := by
  have ha2 : 2 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  have hbase : 3 * b ≤ numeratorBound a b := by
    unfold numeratorBound
    have hh : 3 ≤ a + b - 1 := by omega
    nlinarith
  have hnot (c n : ℕ) (hn : 0 < n) (hc : n < c) : ¬c ∣ n := by
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  by_cases haodd : Odd a
  · have hca : (3 * a).Coprime 2 := (by norm_num : Nat.Coprime 3 2).mul_left haodd.coprime_two_right
    have hc := density_le_gamma_of_conditions (a := a) (b := b) (c := 3 * a) (d := 2)
      (by omega) (by omega) (by nlinarith) (by omega) hca (by omega) (by nlinarith)
      (hnot _ _ ha (by omega)) (hnot _ _ (by omega) (by omega))
    exact (density_lower_left ha).trans hc
  · have hbeven : ¬Even b := by
      intro hbEven
      have haEven : Even a := (Nat.even_or_odd a).resolve_right haodd
      have htwo : 2 ∣ a.gcd b := Nat.dvd_gcd (even_iff_two_dvd.mp haEven) (even_iff_two_dvd.mp hbEven)
      rw [hcop.gcd_eq_one] at htwo
      norm_num at htwo
    have hbodd : Odd b := (Nat.even_or_odd b).resolve_left hbeven
    have hcb2 : (3 * b).Coprime 2 := (by norm_num : Nat.Coprime 3 2).mul_left hbodd.coprime_two_right
    have hcb4 : (3 * b).Coprime 4 := by simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using hcb2.pow_right 2
    have hc := density_le_gamma_of_conditions (a := a) (b := b) (c := 3 * b) (d := 4)
      (by omega) (by omega) hbase (by omega) hcb4 (by omega) (by nlinarith)
      (hnot _ _ ha (by omega)) (hnot _ _ (by omega) (by omega))
    exact (density_lower_right (by omega)).trans hc

theorem gammaReal_ge_one_third {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hb2a : b < 2 * a) (hcop : a.Coprime b) : (1 / 3 : ℝ) ≤ gammaReal a b := by
  have hh := (Rat.cast_le (K := ℝ)).mpr (gamma_ge_one_third ha hab hb2a hcop)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  exact hh

theorem palm_exponent {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hb2a : b < 2 * a) (hcop : a.Coprime b) :
    min (17 / 24 : ℝ) (1 - gammaReal a b) = 1 - gammaReal a b := by
  have hh := gammaReal_ge_one_third ha hab hb2a hcop
  exact min_eq_right (by linarith only [hh])

end PaperP1.FixedChannelGammaLower
