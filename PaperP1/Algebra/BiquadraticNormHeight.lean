module

public import PaperP1.Algebra.BiquadraticSourceNorm
public import PaperP1.Algebra.BivariateHeightPower
public import PaperP1.Algebra.BivariateDegreeArithmetic

/-! # An explicit finite height exponent for the two-witness norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticNormHeight

open Polynomial PaperP1.BivariateDegrees PaperP1.BiquadraticSourceNorm
  PaperP1.PolynomialHeightArithmetic PaperP1.BivariateHeightPower

theorem formula_height (A : Fin 4 → ℤ[X][X]) (F : Fin 3 → ℤ[X][X]) (H : ℤ[X][X])
    (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hAd : ∀ χ, degreeX (A χ) ≤ 3 * q ∧ degreeY (A χ) ≤ 3 * q)
    (hFd : ∀ i, degreeX (F i) ≤ 2 * q ∧ degreeY (F i) ≤ 2 * q)
    (hHd : degreeX H ≤ 2 * q ∧ degreeY H ≤ 2 * q)
    (hAh : ∀ χ, BivariateHeight.height (A χ) ≤ (B + 1) ^ (275 * q))
    (hFh : ∀ i, BivariateHeight.height (F i) ≤ (B + 1) ^ (4 * q))
    (hHh : BivariateHeight.height H ≤ (B + 1) ^ (4 * q)) :
    BivariateHeight.height (sourceNorm (F 0) (F 1) (F 2) H (A 0) (A 1) (A 2) (A 3)) ≤
      (B + 1) ^ (1200 * q) := by
  have hsqD : ∀ χ, degreeX ((A χ) ^ 2) ≤ 6 * q ∧ degreeY ((A χ) ^ 2) ≤ 6 * q := by
    intro χ
    have hp := BivariateDegreeArithmetic.pow_bound (A χ) (3 * q) 2 (hAd χ)
    constructor <;> omega
  have hsqH : ∀ χ, BivariateHeight.height ((A χ) ^ 2) ≤ (B + 1) ^ (562 * q) := by
    intro χ
    simpa only [pow_two] using mul_power (A χ) (A χ) B q 275 275 hq hqB
      (by have h := (hAd χ).1; omega) (by have h := (hAd χ).2; omega) (hAh χ) (hAh χ)
  have htermD : ∀ i : Fin 3, degreeX (F i * (A i.succ) ^ 2) ≤ 8 * q ∧
      degreeY (F i * (A i.succ) ^ 2) ≤ 8 * q := by
    intro i
    have hp := BivariateDegreeArithmetic.mul_bound (F i) ((A i.succ) ^ 2) (2 * q) (6 * q) (hFd i) (hsqD i.succ)
    constructor <;> omega
  have htermH : ∀ i : Fin 3, BivariateHeight.height (F i * (A i.succ) ^ 2) ≤ (B + 1) ^ (578 * q) := by
    intro i
    exact mul_power (F i) ((A i.succ) ^ 2) B q 4 562 hq hqB
      (by have h₁ := (hFd i).1; have h₂ := (hsqD i.succ).1; omega)
      (by have h₁ := (hFd i).2; have h₂ := (hsqD i.succ).2; omega) (hFh i) (hsqH i.succ)
  let U := (A 0) ^ 2 + F 0 * (A 1) ^ 2 - F 1 * (A 2) ^ 2 - F 2 * (A 3) ^ 2
  have hzeroD : degreeX ((A 0) ^ 2) ≤ 8 * q ∧ degreeY ((A 0) ^ 2) ≤ 8 * q := by
    have hz := hsqD 0
    constructor <;> omega
  have hUD : degreeX U ≤ 8 * q ∧ degreeY U ≤ 8 * q :=
    BivariateDegreeArithmetic.sub_bound _ _ _
      (BivariateDegreeArithmetic.sub_bound _ _ _
        (BivariateDegreeArithmetic.add_bound _ _ _ hzeroD (htermD 0)) (htermD 1)) (htermD 2)
  have hzeroH : BivariateHeight.height ((A 0) ^ 2) ≤ (B + 1) ^ (578 * q) :=
    (hsqH 0).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hleftH : BivariateHeight.height ((A 0) ^ 2 + F 0 * (A 1) ^ 2) ≤ (B + 1) ^ (579 * q) :=
    (bivariate_height_add _ _).trans (sum_power B q 578 _ _ hq hqB hzeroH (htermH 0))
  have hrightH : BivariateHeight.height (F 1 * (A 2) ^ 2 + F 2 * (A 3) ^ 2) ≤ (B + 1) ^ (579 * q) :=
    (bivariate_height_add _ _).trans (sum_power B q 578 _ _ hq hqB (htermH 1) (htermH 2))
  have hUH : BivariateHeight.height U ≤ (B + 1) ^ (580 * q) := by
    have he : U = ((A 0) ^ 2 + F 0 * (A 1) ^ 2) - (F 1 * (A 2) ^ 2 + F 2 * (A 3) ^ 2) := by dsimp [U]; ring
    rw [he]
    exact (bivariate_height_sub _ _).trans (sum_power B q 579 _ _ hq hqB hleftH hrightH)
  have hpairD (i j : Fin 4) : degreeX (A i * A j) ≤ 6 * q ∧ degreeY (A i * A j) ≤ 6 * q := by
    have hp := BivariateDegreeArithmetic.mul_bound (A i) (A j) (3 * q) (3 * q) (hAd i) (hAd j)
    constructor <;> omega
  have hpairH (i j : Fin 4) : BivariateHeight.height (A i * A j) ≤ (B + 1) ^ (562 * q) :=
    mul_power (A i) (A j) B q 275 275 hq hqB
      (by have h₁ := (hAd i).1; have h₂ := (hAd j).1; omega)
      (by have h₁ := (hAd i).2; have h₂ := (hAd j).2; omega) (hAh i) (hAh j)
  have hHpairD : degreeX (H * (A 2 * A 3)) ≤ 8 * q ∧ degreeY (H * (A 2 * A 3)) ≤ 8 * q := by
    have hp := BivariateDegreeArithmetic.mul_bound H (A 2 * A 3) (2 * q) (6 * q) hHd (hpairD 2 3)
    constructor <;> omega
  have hHpairH : BivariateHeight.height (H * (A 2 * A 3)) ≤ (B + 1) ^ (578 * q) :=
    mul_power H (A 2 * A 3) B q 4 562 hq hqB
      (by have h₁ := hHd.1; have h₂ := (hpairD 2 3).1; omega)
      (by have h₁ := hHd.2; have h₂ := (hpairD 2 3).2; omega) hHh (hpairH 2 3)
  let V := A 0 * A 1 - H * (A 2 * A 3)
  have hpairZeroD : degreeX (A 0 * A 1) ≤ 8 * q ∧ degreeY (A 0 * A 1) ≤ 8 * q := by
    have hp := hpairD 0 1
    constructor <;> omega
  have hVD : degreeX V ≤ 8 * q ∧ degreeY V ≤ 8 * q :=
    BivariateDegreeArithmetic.sub_bound _ _ _ hpairZeroD hHpairD
  have hpairZeroH : BivariateHeight.height (A 0 * A 1) ≤ (B + 1) ^ (578 * q) :=
    (hpairH 0 1).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hVH : BivariateHeight.height V ≤ (B + 1) ^ (579 * q) :=
    (bivariate_height_sub _ _).trans (sum_power B q 578 _ _ hq hqB hpairZeroH hHpairH)
  have hU₂H : BivariateHeight.height (U ^ 2) ≤ (B + 1) ^ (1172 * q) := by
    simpa only [pow_two] using mul_power U U B q 580 580 hq hqB
      (by have h := hUD.1; omega) (by have h := hUD.2; omega) hUH hUH
  have hV₂H : BivariateHeight.height (V ^ 2) ≤ (B + 1) ^ (1170 * q) := by
    simpa only [pow_two] using mul_power V V B q 579 579 hq hqB
      (by have h := hVD.1; omega) (by have h := hVD.2; omega) hVH hVH
  have hV₂D : degreeX (V ^ 2) ≤ 16 * q ∧ degreeY (V ^ 2) ≤ 16 * q := by
    have hp := BivariateDegreeArithmetic.pow_bound V (8 * q) 2 hVD
    constructor <;> omega
  have hFVH : BivariateHeight.height (F 0 * V ^ 2) ≤ (B + 1) ^ (1186 * q) :=
    mul_power (F 0) (V ^ 2) B q 4 1170 hq hqB
      (by have h₁ := (hFd 0).1; have h₂ := hV₂D.1; omega)
      (by have h₁ := (hFd 0).2; have h₂ := hV₂D.2; omega) (hFh 0) hV₂H
  have hfourH : BivariateHeight.height (4 * (F 0 * V ^ 2)) ≤ (B + 1) ^ (1188 * q) :=
    scalar_four (F 0 * V ^ 2) B q 1186 hq hqB hFVH
  have hU₂H' : BivariateHeight.height (U ^ 2) ≤ (B + 1) ^ (1188 * q) :=
    hU₂H.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hn : BivariateHeight.height (U ^ 2 - 4 * (F 0 * V ^ 2)) ≤ (B + 1) ^ (1189 * q) :=
    (bivariate_height_sub _ _).trans (sum_power B q 1188 _ _ hq hqB hU₂H' hfourH)
  have he : sourceNorm (F 0) (F 1) (F 2) H (A 0) (A 1) (A 2) (A 3) = U ^ 2 - 4 * (F 0 * V ^ 2) := by
    dsimp [sourceNorm, U, V]
    ring
  rw [he]
  exact hn.trans (Nat.pow_le_pow_right (by omega) (by omega))

end PaperP1.BiquadraticNormHeight
