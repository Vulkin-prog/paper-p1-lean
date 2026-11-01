module

public import PaperP1.Arithmetic.FixedChannelGamma
public import PaperP1.Arithmetic.UnionMatchDensity

/-! # Uniform finite matching bounds at every admissible rational height -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.FixedChannelMatches

open PaperP1.ChannelMatchDensity PaperP1.FixedChannelGamma PaperP1.UnionMatchDensity

theorem large_numerator_density_lt_base {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcB : numeratorBound a b < c) : density a b c < 1 / (b : ℚ) := by
  have hc : 0 < c := by omega
  have hga : c.gcd a ≤ a := Nat.le_of_dvd ha (Nat.gcd_dvd_right c a)
  have hgb : c.gcd b ≤ b := Nat.le_of_dvd hb (Nat.gcd_dvd_right c b)
  have hsum : c.gcd a + c.gcd b - 1 ≤ a + b - 1 := by omega
  have hmul := Nat.mul_le_mul_left b hsum
  have hNat : (c.gcd a + c.gcd b - 1) * b < c := by
    unfold numeratorBound at hcB
    nlinarith
  unfold density
  apply (div_lt_div_iff₀ (by exact_mod_cast hc : (0 : ℚ) < c)
    (by exact_mod_cast hb : (0 : ℚ) < b)).mpr
  norm_num only [one_mul]
  exact_mod_cast hNat

theorem density_le_gamma_all {a b c d : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a)
    (hca : ¬c ∣ a) (hcb : ¬c ∣ b) : density a b c ≤ gamma a b := by
  by_cases hcB : c ≤ numeratorBound a b
  · have hratio := (ratio_conditions hd).mp ⟨hlo, hhi⟩
    exact density_le_gamma_of_conditions (by omega) hc hcB hd hcop hratio.1 hratio.2 hca hcb
  · exact (large_numerator_density_lt_base ha (by omega) (by omega : numeratorBound a b < c)).le.trans
      (base_le_gamma a b)

theorem window_match_gamma {a b c d : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a)
    (hca : ¬c ∣ a) (hcb : ¬c ∣ b) (h : ℤ) (L : ℕ) :
    ((matchOffsets a b c d h (-1) L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) * gamma a b + 3 := by
  have hbound := window_match_upper hab hc hcop h L
  have hgamma := density_le_gamma_all ha hb hc hd hcop hlo hhi hca hcb
  have hmul := mul_le_mul_of_nonneg_left hgamma (Nat.cast_nonneg (α := ℚ) (L + 1))
  linarith

theorem real_abs_match_error {a b c d : ℕ} (hab : a.Coprime b) (hc : 0 < c) (hcop : c.Coprime d)
    (h lo hi : ℤ) (hinterval : lo ≤ hi) :
    |((matchOffsets a b c d h lo hi).card : ℝ) - ((hi - lo : ℤ) : ℝ) * (density a b c : ℚ)| ≤ 3 := by
  have hQ := abs_match_error hab hc hcop h lo hi hinterval
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat] at hR
  exact hR

theorem window_match_gamma_real {a b c d : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a)
    (hca : ¬c ∣ a) (hcb : ¬c ∣ b) (h : ℤ) (L : ℕ) :
    ((matchOffsets a b c d h (-1) L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3 := by
  have hQ := window_match_gamma ha hb hab hc hd hcop hlo hhi hca hcb h L
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hR
  exact hR

theorem window_match_two_three {c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hlo : (3 : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 4)
    (hca : ¬c ∣ 2) (hcb : ¬c ∣ 3) (h : ℤ) (L : ℕ) :
    ((matchOffsets 2 3 c d h (-1) L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) / 3 + 3 := by
  have hbound := window_match_gamma (by norm_num : 0 < 2) (by norm_num : 3 ≤ 3)
    (by norm_num : Nat.Coprime 2 3) hc hd hcop hlo (by convert hhi using 1; norm_num) hca hcb h L
  simpa only [gamma_two_three, mul_one_div] using hbound

theorem window_match_three_four {c d : ℕ} (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hlo : (2 : ℚ) < (c : ℚ) / d) (hhi : (c : ℚ) / d < 6)
    (hca : ¬c ∣ 3) (hcb : ¬c ∣ 4) (h : ℤ) (L : ℕ) :
    ((matchOffsets 3 4 c d h (-1) L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) / 2 + 3 := by
  have hbound := window_match_gamma (by norm_num : 0 < 3) (by norm_num : 3 ≤ 4)
    (by norm_num : Nat.Coprime 3 4) hc hd hcop (by convert hlo using 1; norm_num)
      (by convert hhi using 1; norm_num) hca hcb h L
  simpa only [gamma_three_four, mul_one_div] using hbound

theorem physical_fraction_of_divisor {a b c d : ℕ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hlo : b * d < 2 * c) (hdiv : c ∣ a ∨ c ∣ b) : (c = a ∨ c = b) ∧ d = 1 := by
  have hmul1 : b ≤ b * d := by simpa using Nat.mul_le_mul_left b (show 1 ≤ d by omega)
  have hc_eq : c = a ∨ c = b := by
    rcases hdiv with hca | hcb
    · left
      have hcle : c ≤ a := Nat.le_of_dvd ha hca
      by_contra hne
      have hclt : c < a := by omega
      have htwice := twice_proper_divisor hca hclt
      omega
    · right
      have hcle : c ≤ b := Nat.le_of_dvd (by omega) hcb
      by_contra hne
      have hclt : c < b := by omega
      have htwice := twice_proper_divisor hcb hclt
      omega
  refine ⟨hc_eq, ?_⟩
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hmul2 : 2 * b ≤ b * d := by simpa only [mul_comm 2 b] using Nat.mul_le_mul_left b hd2
  rcases hc_eq with rfl | rfl <;> omega

end PaperP1.FixedChannelMatches
