module

public import PaperP1.Combinatorics.RungeCoefficients
public import Mathlib.Tactic.NormNum

/-! # Common denominators and finite bounds for two-variable square-root branch coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateRungeCoefficients

open Finset PaperP1.RungeCoefficients

theorem weakComposition_bound (d m : ℕ) : Fintype.card (WeakComposition d m) ≤ 2 ^ (m + d) := by
  rw [card_weakComposition]
  exact (Nat.choose_le_two_pow (d + m - 1) m).trans
    (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega))

theorem coefficient_bound {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) (B : ℚ) (hB : 0 ≤ B)
    (hγ : ∀ i, |(γ i : ℚ)| ≤ B) :
    |rungeCoefficient γ m| ≤ (2 : ℚ) ^ (m + d) * B ^ m := by
  exact (abs_rungeCoefficient_le_card_mul hγ).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast weakComposition_bound d m) (pow_nonneg hB m))

theorem product_bound {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) (a b : ℕ)
    (B : ℚ) (hB : 0 ≤ B) (hγ : ∀ i, |(γ i : ℚ)| ≤ B) (hδ : ∀ i, |(δ i : ℚ)| ≤ B) :
    |rungeCoefficient γ a * rungeCoefficient δ b| ≤ (2 : ℚ) ^ (a + b + d + e) * B ^ (a + b) := by
  rw [abs_mul]
  calc
    _ ≤ ((2 : ℚ) ^ (a + d) * B ^ a) * ((2 : ℚ) ^ (b + e) * B ^ b) :=
      mul_le_mul (coefficient_bound γ a B hB hγ) (coefficient_bound δ b B hB hδ)
        (abs_nonneg _) (by positivity)
    _ = _ := by simp only [pow_add]; ring

theorem scaled_product_integral {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (T a b : ℕ) (hab : a + b ≤ T) :
    IsRatInteger ((2 : ℚ) ^ (2 * T) * (rungeCoefficient γ a * rungeCoefficient δ b)) := by
  obtain ⟨z, hz⟩ := (two_pow_two_mul_rungeCoefficient_isRatInteger γ a).mul
    (two_pow_two_mul_rungeCoefficient_isRatInteger δ b)
  refine ⟨(2 : ℤ) ^ (2 * (T - (a + b))) * z, ?_⟩
  push_cast
  rw [← hz, show 2 * T = 2 * (T - (a + b)) + 2 * a + 2 * b by omega, pow_add, pow_add]
  ring

def scaledCoefficient {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (T a b : ℕ) (hab : a + b ≤ T) : ℤ :=
  Classical.choose (scaled_product_integral γ δ T a b hab)

theorem scaledCoefficient_spec {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (T a b : ℕ) (hab : a + b ≤ T) :
    (scaledCoefficient γ δ T a b hab : ℚ) =
      (2 : ℚ) ^ (2 * T) * (rungeCoefficient γ a * rungeCoefficient δ b) :=
  (Classical.choose_spec (scaled_product_integral γ δ T a b hab)).symm

theorem scaled_height {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (B q a b : ℕ) (hB : 1 ≤ B) (hab : a + b ≤ 6 * q) (hde : d + e ≤ 4 * q)
    (hγ : ∀ i, |γ i| ≤ (B : ℤ)) (hδ : ∀ i, |δ i| ≤ (B : ℤ)) :
    |scaledCoefficient γ δ (6 * q) a b hab| ≤ ((B + 1) ^ (28 * q) : ℕ) := by
  have hB0 : (0 : ℚ) ≤ B := by positivity
  have hbase : (2 : ℚ) ≤ B + 1 := by exact_mod_cast (show 2 ≤ B + 1 by omega)
  have hbase1 : (1 : ℚ) ≤ B + 1 := by linarith only [hbase]
  have hγQ : ∀ i, |(γ i : ℚ)| ≤ (B : ℚ) := fun i ↦ by exact_mod_cast hγ i
  have hδQ : ∀ i, |(δ i : ℚ)| ≤ (B : ℚ) := fun i ↦ by exact_mod_cast hδ i
  have hp := product_bound γ δ a b B hB0 hγQ hδQ
  have hheight : |(scaledCoefficient γ δ (6 * q) a b hab : ℚ)| ≤ ((B : ℚ) + 1) ^ (28 * q) := by
    rw [scaledCoefficient_spec, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)]
    calc
      _ ≤ (2 : ℚ) ^ (2 * (6 * q)) * ((2 : ℚ) ^ (a + b + d + e) * (B : ℚ) ^ (a + b)) :=
        mul_le_mul_of_nonneg_left hp (pow_nonneg (by norm_num) _)
      _ = (2 : ℚ) ^ (2 * (6 * q) + a + b + d + e) * (B : ℚ) ^ (a + b) := by
        simp only [pow_add]
        ring
      _ ≤ ((B : ℚ) + 1) ^ (2 * (6 * q) + a + b + d + e) * ((B : ℚ) + 1) ^ (a + b) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hbase _)
          (pow_le_pow_left₀ hB0 (by linarith) _) (pow_nonneg hB0 _) (by positivity)
      _ = ((B : ℚ) + 1) ^ ((2 * (6 * q) + a + b + d + e) + (a + b)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase1 (by omega)
  exact_mod_cast hheight

end PaperP1.BivariateRungeCoefficients
