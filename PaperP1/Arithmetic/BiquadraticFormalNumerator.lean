module

public import PaperP1.Arithmetic.BiquadraticRungeMatrix
public import PaperP1.Analysis.RungePowerSeries

/-! # The actual two-variable square-root numerator has the prescribed vanishing coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticFormalNumerator

open Finset PaperP1.RungeCoefficients PaperP1.RungePowerSeries
  PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix

abbrev Series := PowerSeries (PowerSeries ℚ)

def coefficient (a b : ℕ) (f : Series) : ℚ :=
  PowerSeries.coeff a (PowerSeries.coeff b f)

def branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) : Series :=
  PowerSeries.C (rungeProductSeries γ) *
    PowerSeries.map (PowerSeries.C (R := ℚ)) (rungeProductSeries δ)

def shift (sx sy : ℕ) (f : Series) : Series :=
  (PowerSeries.X : Series) ^ sy * (PowerSeries.C ((PowerSeries.X : PowerSeries ℚ) ^ sx) * f)

theorem coefficient_branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) (a b : ℕ) :
    coefficient a b (branch γ δ) = rungeCoefficient γ a * rungeCoefficient δ b := by
  rw [coefficient, branch, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
    PowerSeries.coeff_mul_C, coeff_rungeProductSeries, coeff_rungeProductSeries]

theorem coefficient_shift (sx sy a b : ℕ) (f : Series) :
    coefficient a b (shift sx sy f) =
      if sx ≤ a ∧ sy ≤ b then coefficient (a - sx) (b - sy) f else 0 := by
  unfold coefficient shift
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hy : sy ≤ b
  · rw [ite_eq_left hy, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hx : sx ≤ a
    · simp only [hx, hy, true_and, ite_true]
    · simp only [hx, false_and, ite_false]
  · rw [ite_eq_right hy]
    simp only [map_zero, hy, and_false, ite_false]

theorem coefficient_sum {ι : Type*} (S : Finset ι) (f : ι → Series) (a b : ℕ) :
    coefficient a b (∑ i ∈ S, f i) = ∑ i ∈ S, coefficient a b (f i) := by
  unfold coefficient
  rw [map_sum, map_sum]

theorem coefficient_scalar (c : ℚ) (f : Series) (a b : ℕ) :
    coefficient a b (PowerSeries.C (PowerSeries.C c) * f) = c * coefficient a b f := by
  rw [coefficient, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  rfl

def numerator {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (w : CoefficientIndex q r s → ℤ) : Series :=
  ∑ i, PowerSeries.C (PowerSeries.C (w i : ℚ)) *
    shift (xShift i) (yShift i) (branch (γ (character i)) (δ (character i)))

theorem coefficient_numerator {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (w : CoefficientIndex q r s → ℤ) (j : EquationIndex q) :
    coefficient j.1.val j.2.val (numerator γ δ w) =
      ∑ i, rationalEntry γ δ j i * (w i : ℚ) := by
  unfold numerator
  rw [coefficient_sum]
  simp_rw [coefficient_scalar, coefficient_shift, coefficient_branch]
  apply sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem exists_vanishing_numerator {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((B + 1) ^ (266 * q) : ℕ)) ∧
        ∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0 := by
  obtain ⟨w, hne, hheight, hzero⟩ := exists_coefficients B hq hqB hr hs γ δ hγ hδ
  refine ⟨w, hne, hheight, ?_⟩
  intro a b hab
  have ha : a < 6 * q + 1 := by omega
  let ja : Fin (6 * q + 1) := ⟨a, ha⟩
  have hb : b < 6 * q + 1 - ja.val := by change b < 6 * q + 1 - a; omega
  let j : EquationIndex q := ⟨ja, ⟨b, hb⟩⟩
  exact (coefficient_numerator γ δ w j).trans (hzero j)

end PaperP1.BiquadraticFormalNumerator
