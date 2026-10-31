module

public import PaperP1.Probability.FiniteCoupling
public import Mathlib.Tactic.Linarith

/-! # Moment transfer for ordered counts on the same finite sample

A deterministic truncation gives the small-disagreement/high-moment estimate.
No independence, bounded-count constant or target moment-transfer bound is
assumed. The higher moment appears explicitly on the right-hand side.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open PaperP1.Algebra Finset

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
theorem ordered_power_difference_bound (Z W : Ω → ℕ)
    (j q : ℕ) (hjq : j ≤ q) (R : ℝ) (hR : 0 < R) (ω : Ω) :
    (Z ω : ℝ) ^ j - (W ω : ℝ) ^ j ≤
      R ^ j * (if Z ω ≠ W ω then 1 else 0) + (Z ω : ℝ) ^ q / R ^ (q - j) := by
  have hZ : (0 : ℝ) ≤ Z ω := Nat.cast_nonneg _
  have hW : (0 : ℝ) ≤ W ω := Nat.cast_nonneg _
  have htail : 0 ≤ (Z ω : ℝ) ^ q / R ^ (q - j) :=
    div_nonneg (pow_nonneg hZ _) (pow_nonneg hR.le _)
  by_cases heq : Z ω = W ω
  · simp only [heq, ne_eq, not_true_eq_false, ↓reduceIte, sub_self, mul_zero, zero_add]
    exact div_nonneg (pow_nonneg hW _) (pow_nonneg hR.le _)
  · simp only [heq, ne_eq, not_false_eq_true, ↓reduceIte, mul_one]
    by_cases hsmall : (Z ω : ℝ) ≤ R
    · have hzj := pow_le_pow_left₀ hZ hsmall j
      have hwj := pow_nonneg hW j
      linarith
    · have hlarge : R ≤ (Z ω : ℝ) := le_of_not_ge hsmall
      have hpow := pow_le_pow_left₀ hR.le hlarge (q - j)
      have hprod := mul_le_mul_of_nonneg_left hpow (pow_nonneg hZ j)
      have hsum : j + (q - j) = q := by omega
      rw [← pow_add, hsum] at hprod
      have hbound : (Z ω : ℝ) ^ j ≤ (Z ω : ℝ) ^ q / R ^ (q - j) :=
        (le_div_iff₀ (pow_pos hR _)).mpr hprod
      have hwj := pow_nonneg hW j
      have hrj := pow_nonneg hR.le j
      linarith

theorem ordered_moment_difference_bound (P : FiniteProbability Ω)
    (Z W : Ω → ℕ) (hWZ : ∀ ω, W ω ≤ Z ω)
    (j q : ℕ) (hjq : j ≤ q) (R : ℝ) (hR : 0 < R) :
    |finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ) ^ j) -
      finiteExpectation P.weight (fun ω ↦ (W ω : ℝ) ^ j)| ≤
        R ^ j * disagreementProbability P Z W +
          finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ) ^ q) / R ^ (q - j) := by
  classical
  have hm : finiteExpectation P.weight (fun ω ↦ (W ω : ℝ) ^ j) ≤
      finiteExpectation P.weight (fun ω ↦ (Z ω : ℝ) ^ j) := by
    apply finiteExpectation_mono
    intro ω
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hWZ ω) j
  rw [abs_of_nonneg (sub_nonneg.mpr hm), ← finiteExpectation_sub]
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦ R ^ j * (if Z ω ≠ W ω then 1 else 0) +
        (Z ω : ℝ) ^ q / R ^ (q - j)) :=
      finiteExpectation_mono P (ordered_power_difference_bound Z W j q hjq R hR)
    _ = _ := by
      rw [finiteExpectation_add, finiteExpectation_const_mul]
      simp only [div_eq_mul_inv, finiteExpectation_mul_const, disagreementProbability]

end PaperP1.Probability
