module

public import PaperP1.Algebra.BivariateBranchBounds
public import PaperP1.Algebra.BivariateHeightPower

/-! # The actual reduced numerator has a geometric majorant with explicit height exponent 300 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticNumeratorBounds

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateBranchBounds
  PaperP1.BiquadraticRungeMatrix PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticNumeratorFactor

theorem finite_bound {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X]) (kx ky H B q : ℕ)
    (hB : 1 ≤ B) (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (hA : ∀ χ, degreeX (A χ) ≤ kx - blockRank r χ ∧ degreeY (A χ) ≤ ky - blockRank s χ)
    (hH : ∀ χ, BivariateHeight.height (A χ) ≤ H)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) (a b : ℕ) :
    |coefficient a b (fromPolynomials A kx ky γ δ)| ≤
      (4 : ℚ) * (((kx + 1) * (ky + 1) : ℕ) : ℚ) * (H : ℚ) * (2 : ℚ) ^ (4 * q) *
        (2 * (B : ℚ)) ^ (a + b) := by
  unfold fromPolynomials
  rw [coefficient_sum]
  calc
    _ ≤ ∑ χ : Fin 4, |coefficient a b
        (BivariateReciprocalSeries.reciprocal (A χ) (kx - blockRank r χ) (ky - blockRank s χ) *
          branch (γ χ) (δ χ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _χ : Fin 4,
        (((kx + 1) * (ky + 1) : ℕ) : ℚ) * (H : ℚ) * (2 : ℚ) ^ (4 * q) * (2 * (B : ℚ)) ^ (a + b) := by
      apply sum_le_sum
      intro χ _
      have hcount : (kx - blockRank r χ + 1) * (ky - blockRank s χ + 1) ≤ (kx + 1) * (ky + 1) :=
        Nat.mul_le_mul (Nat.add_le_add_right (Nat.sub_le _ _) 1) (Nat.add_le_add_right (Nat.sub_le _ _) 1)
      have hcountQ : (((kx - blockRank r χ + 1) * (ky - blockRank s χ + 1) : ℕ) : ℚ) ≤
          (((kx + 1) * (ky + 1) : ℕ) : ℚ) := by exact_mod_cast hcount
      have hrχ := rank_bound q r hr χ
      have hsχ := rank_bound q s hs χ
      have hpower : (2 : ℚ) ^ (2 * blockRank r χ + 2 * blockRank s χ) ≤ (2 : ℚ) ^ (4 * q) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact (reciprocal_branch_bound (γ χ) (δ χ) (A χ) _ _ H B (hA χ).1 (hA χ).2
        (hH χ) hB (hγ χ) (hδ χ) a b).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_right hcountQ (by positivity)) hpower (by positivity) (by positivity))
            (by positivity))
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
      ring

theorem constant_budget (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) :
    4 * (3 * q + 1) ^ 2 * (B + 1) ^ (275 * q) * 2 ^ (4 * q) ≤ (B + 1) ^ (300 * q) := by
  have hlinear := BivariateDivisionBounds.linear_dimension_power B q hq hqB
  have ht := BivariateHeightPower.two_le_power B q hq (hq.trans hqB)
  have hfour : 4 ≤ (B + 1) ^ (2 * q) := by
    calc
      4 = 2 * 2 := rfl
      _ ≤ (B + 1) ^ q * (B + 1) ^ q := Nat.mul_le_mul ht ht
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hdim : (3 * q + 1) ^ 2 ≤ (B + 1) ^ (6 * q) := by
    calc
      _ ≤ ((B + 1) ^ (3 * q)) ^ 2 := Nat.pow_le_pow_left hlinear 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have htwo : 2 ^ (4 * q) ≤ (B + 1) ^ (4 * q) := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ (B + 1) ^ (2 * q) * (B + 1) ^ (6 * q) * (B + 1) ^ (275 * q) * (B + 1) ^ (4 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hfour hdim) le_rfl) htwo
    _ = (B + 1) ^ (287 * q) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem geometric_bound {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X]) (kx ky B q : ℕ)
    (hq : 1 ≤ q) (hqB : q ≤ B) (hkx : kx ≤ 3 * q) (hky : ky ≤ 3 * q)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (hA : ∀ χ, degreeX (A χ) ≤ kx - blockRank r χ ∧ degreeY (A χ) ≤ ky - blockRank s χ)
    (hH : ∀ χ, BivariateHeight.height (A χ) ≤ (B + 1) ^ (275 * q))
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) (a b : ℕ) :
    |coefficient a b (fromPolynomials A kx ky γ δ)| ≤
      ((B : ℚ) + 1) ^ (300 * q) * (2 * (B : ℚ)) ^ (a + b) := by
  have hfinite := finite_bound A kx ky ((B + 1) ^ (275 * q)) B q (hq.trans hqB) hr hs hA hH γ δ hγ hδ a b
  have hcount : (kx + 1) * (ky + 1) ≤ (3 * q + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (Nat.add_le_add_right hkx 1) (Nat.add_le_add_right hky 1)
  have hconstant : (4 : ℚ) * (((3 * q + 1) ^ 2 : ℕ) : ℚ) * ((B + 1) ^ (275 * q) : ℕ) *
      (2 : ℚ) ^ (4 * q) ≤ ((B : ℚ) + 1) ^ (300 * q) := by exact_mod_cast constant_budget B q hq hqB
  have hcountQ : (((kx + 1) * (ky + 1) : ℕ) : ℚ) ≤ (((3 * q + 1) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hcount
  exact hfinite.trans (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcountQ (by norm_num))
      (by positivity)) (by positivity)).trans hconstant) (by positivity))

end PaperP1.BiquadraticNumeratorBounds
