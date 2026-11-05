module

public import PaperP1.Diophantine.AffineMonomialDeterminant
public import PaperP1.Analysis.LocalDeterminantDegreeChoice

/-! # The exact affine row weights permit a prime scale 1/b+epsilon

Only the auxiliary rectangle and its numerical comparison are chosen here.
The global curve count is not an assumption or a conclusion of this module.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineDeterminantDegreeChoice

open AffineMonomialDeterminant

theorem exists_auxiliary_degree (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧
      let J := b - 1
      let k := (A + 1) * (J + 1)
      let v := k * (k - 1) / 2
      1 ≤ v ∧ (weightSum A J : ℝ) ≤ (1 / (b : ℝ) + ε / 2) * v := by
  obtain ⟨A, hAgt⟩ := exists_nat_gt (max 1 (8 * ((b : ℝ) + 1) / ε))
  have hA : 1 ≤ A := by exact_mod_cast ((le_max_left _ _).trans_lt hAgt).le
  refine ⟨A, hA, ?_⟩
  let J := b - 1
  let k := (A + 1) * (J + 1)
  let v := k * (k - 1) / 2
  change 1 ≤ v ∧ (weightSum A J : ℝ) ≤ (1 / (b : ℝ) + ε / 2) * v
  have hJ : J + 1 = b := by dsimp only [J]; omega
  have hk : k = (A + 1) * b := by dsimp only [k]; rw [hJ]
  have hkfour : 4 ≤ k := by rw [hk]; nlinarith
  obtain ⟨hv, htwov⟩ := LocalDeterminantDegreeChoice.triangle_weight k (by omega)
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbp : (0 : ℝ) < b := by linarith
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hkR : (k : ℝ) = ((A : ℝ) + 1) * b := by rw [hk]; push_cast; rfl
  have hJR : (J : ℝ) = (b : ℝ) - 1 := by dsimp only [J]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbig : 8 * ((b : ℝ) + 1) < ε * A := by
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hAgt)
    nlinarith
  have hkA : (A : ℝ) ≤ (k : ℝ) - 1 := by
    rw [hkR]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A + 1) (by linarith : (0 : ℝ) ≤ b - 2)]
  have hεk := mul_le_mul_of_nonneg_left hkA hε.le
  have hdiv : (A : ℝ) ≤ (1 / (b : ℝ)) * ((k : ℝ) - 1) := by
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ hbp).mpr
    rw [hkR]
    nlinarith
  have hweight : (A : ℝ) + J ≤ (1 / (b : ℝ) + ε / 2) * ((k : ℝ) - 1) := by
    rw [hJR]
    nlinarith
  have htwow : (2 : ℝ) * (weightSum A J : ℝ) = (k : ℝ) * ((A : ℝ) + J) := by
    have hh := weight_sum_twice A J
    change 2 * weightSum A J = k * (A + J) at hh
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right hweight (Nat.cast_nonneg (α := ℝ) k)
  refine ⟨hv, ?_⟩
  have hh : (2 : ℝ) * (weightSum A J : ℝ) ≤ (1 / (b : ℝ) + ε / 2) * (2 * (v : ℝ)) := by
    rw [htwov, htwow]
    nlinarith
  nlinarith

theorem determinant_small (A J v : ℕ) (C B V α β P : ℝ)
    (hC : 1 ≤ C) (hfact : (((A + 1) * (J + 1)).factorial : ℝ) < C)
    (hB : 1 ≤ B) (hV : 1 ≤ V) (hv : 1 ≤ v)
    (hweight : (weightSum A J : ℝ) ≤ α * v) (hβ : 0 ≤ β)
    (hP : C * B ^ α * V ^ β ≤ P) :
    (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J < P ^ v := by
  have hh := MonomialPrimeScale.strict_power_domination C
    (((A + 1) * (J + 1)).factorial : ℝ) B V α β P (weightSum A J) 0 v
    hC hfact hB hV hv hweight
    (by simpa only [Nat.cast_zero] using mul_nonneg hβ (Nat.cast_nonneg (α := ℝ) v)) hP
  simpa only [pow_zero, mul_one] using hh

end PaperP1.AffineDeterminantDegreeChoice
