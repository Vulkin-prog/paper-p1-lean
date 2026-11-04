module

public import PaperP1.Arithmetic.BoundedReducedBinaryBasis

/-! # A common power bound for the explicit reduced-basis height polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedBasisPolynomialBound

open PaperP1.BoundedReducedBinaryBasis

theorem double_power (J n : ℕ) (hJ : 2 ≤ J) : 2 * J ^ n ≤ J ^ (n + 1) := by
  rw [pow_succ']
  exact Nat.mul_le_mul_right _ hJ

theorem add_power (J n a b : ℕ) (hJ : 2 ≤ J) (ha : a ≤ J ^ n) (hb : b ≤ J ^ n) :
    a + b ≤ J ^ (n + 1) := by
  calc
    _ ≤ J ^ n + J ^ n := Nat.add_le_add ha hb
    _ = 2 * J ^ n := by ring
    _ ≤ _ := double_power J n hJ

theorem vector_height_bound (J : ℕ) (hJ : 2 ≤ J) : vectorHeight J ≤ J ^ 7 := by
  have hJ0 : 0 < J := by omega
  have h4 : 4 * J ^ 4 ≤ J ^ 6 := by
    calc
      _ = 2 * (2 * J ^ 4) := by ring
      _ ≤ 2 * J ^ 5 := Nat.mul_le_mul_left 2 (double_power J 4 hJ)
      _ ≤ _ := double_power J 5 hJ
  exact add_power J 6 _ 1 hJ h4 (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))

theorem completion_height_bound (J : ℕ) (hJ : 2 ≤ J) : completionHeight J ≤ J ^ 16 := by
  have hJ0 : 0 < J := by omega
  have hH := vector_height_bound J hJ
  have hsq : vectorHeight J ^ 2 ≤ J ^ 14 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.zero_le (vectorHeight J)) hH 2
  have hsmall : vectorHeight J ≤ J ^ 14 := hH.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hsum := add_power J 14 _ _ hJ hsq hsmall
  exact add_power J 15 _ 1 hJ hsum (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))

theorem second_energy_height_bound (J : ℕ) (hJ : 2 ≤ J) :
    8 * J ^ 2 * completionHeight J ^ 2 ≤ J ^ 37 := by
  have hs : completionHeight J ^ 2 ≤ J ^ 32 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.zero_le (completionHeight J)) (completion_height_bound J hJ) 2
  calc
    _ ≤ 8 * J ^ 2 * J ^ 32 := Nat.mul_le_mul_left _ hs
    _ = 8 * J ^ 34 := by rw [mul_assoc, ← pow_add]
    _ = 2 * (2 * (2 * J ^ 34)) := by ring
    _ ≤ 2 * (2 * J ^ 35) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 (double_power J 34 hJ))
    _ ≤ 2 * J ^ 36 := Nat.mul_le_mul_left 2 (double_power J 35 hJ)
    _ ≤ _ := double_power J 36 hJ

theorem projection_height_bound (J : ℕ) (hJ : 2 ≤ J) : projectionHeight J ≤ J ^ 42 := by
  have hJ0 : 0 < J := by omega
  have hd : 2 * J ^ 2 ≤ J ^ 3 := double_power J 2 hJ
  have hsmall : 2 * J ^ 2 ≤ J ^ 37 := hd.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hsum := add_power J 37 _ _ hJ hsmall (second_energy_height_bound J hJ)
  have hprod : 2 * J ^ 2 * (2 * J ^ 2 + 8 * J ^ 2 * completionHeight J ^ 2) ≤ J ^ 41 := by
    calc
      _ ≤ J ^ 3 * J ^ 38 := Nat.mul_le_mul hd hsum
      _ = _ := by rw [← pow_add]
  exact add_power J 41 _ 1 hJ hprod (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))

theorem basis_height_bound (J : ℕ) (hJ : 2 ≤ J) : basisHeight J ≤ J ^ 60 := by
  have hJ0 : 0 < J := by omega
  have hplus : projectionHeight J + 1 ≤ J ^ 43 :=
    add_power J 42 _ 1 hJ (projection_height_bound J hJ) (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  calc
    _ ≤ 2 * J ^ 16 * J ^ 43 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (completion_height_bound J hJ)) hplus
    _ = 2 * J ^ 59 := by rw [mul_assoc, ← pow_add]
    _ ≤ _ := double_power J 59 hJ

end PaperP1.ReducedBasisPolynomialBound
