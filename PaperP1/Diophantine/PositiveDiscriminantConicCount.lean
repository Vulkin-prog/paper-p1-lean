module

public import PaperP1.Diophantine.SignedQuadraticCount
public import PaperP1.Algebra.ConicPolynomialPresentation

/-! # Unconditional polynomial-height counts for conics of positive discriminant

The leading quadratic coefficient and norm constant are explicitly nonzero.
All signs of the actual integer coordinates are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveDiscriminantConicCount

open Polynomial Finset PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation

theorem constant_mul_power (N : ℕ) (hN : 2 ≤ N) (a j r : ℕ) (ha : a ≤ 2 ^ j) :
    a * N ^ r ≤ N ^ (r + j) := by
  calc
    _ ≤ N ^ j * N ^ r := Nat.mul_le_mul_right _ (ha.trans (Nat.pow_le_pow_left hN j))
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem polynomial_budget (Q : Coefficients) (N K H : ℕ) (hN : 2 ≤ N)
    (hM : height Q ≤ N ^ K) (hH : H ≤ N ^ K) :
    (discriminant Q).natAbs ≤ N ^ (4 * K + 8) ∧
      (normConstant Q).natAbs ≤ N ^ (4 * K + 8) ∧
      (10 * H + 6) * height Q ^ 2 ≤ N ^ (4 * K + 8) ∧
        (6 * H + 2) * height Q ≤ N ^ (4 * K + 8) := by
  have hpow : 1 ≤ N ^ K := Nat.one_le_pow _ _ (by omega)
  have hmon (r s : ℕ) (hrs : r ≤ s) : N ^ r ≤ N ^ s := Nat.pow_le_pow_right (by omega) hrs
  have hΔ : (discriminant Q).natAbs ≤ N ^ (4 * K + 8) := by
    calc
      _ ≤ 5 * height Q ^ 2 := discriminant_bound Q
      _ ≤ 5 * (N ^ K) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2)
      _ = 5 * N ^ (2 * K) := by rw [← pow_mul, Nat.mul_comm K 2]
      _ ≤ N ^ (2 * K + 3) := constant_mul_power N hN 5 3 (2 * K) (by decide)
      _ ≤ _ := hmon _ _ (by omega)
  have hδ : (normConstant Q).natAbs ≤ N ^ (4 * K + 8) := by
    calc
      _ ≤ 136 * height Q ^ 4 := normConstant_bound Q
      _ ≤ 136 * (N ^ K) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 4)
      _ = 136 * N ^ (4 * K) := by rw [← pow_mul, Nat.mul_comm K 4]
      _ ≤ _ := constant_mul_power N hN 136 8 (4 * K) (by decide)
  have hu : (10 * H + 6) * height Q ^ 2 ≤ N ^ (4 * K + 8) := by
    calc
      _ ≤ (16 * N ^ K) * (N ^ K) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hM 2)
      _ = 16 * (N ^ K) ^ 3 := by ring
      _ = 16 * N ^ (3 * K) := by rw [← pow_mul, Nat.mul_comm K 3]
      _ ≤ N ^ (3 * K + 4) := constant_mul_power N hN 16 4 (3 * K) (by decide)
      _ ≤ _ := hmon _ _ (by omega)
  have hv : (6 * H + 2) * height Q ≤ N ^ (4 * K + 8) := by
    calc
      _ ≤ (8 * N ^ K) * N ^ K := Nat.mul_le_mul (by omega) hM
      _ = 8 * (N ^ K) ^ 2 := by ring
      _ = 8 * N ^ (2 * K) := by rw [← pow_mul, Nat.mul_comm K 2]
      _ ≤ N ^ (2 * K + 3) := constant_mul_power N hN 8 3 (2 * K) (by decide)
      _ ≤ _ := hmon _ _ (by omega)
  exact ⟨hΔ, hδ, hu, hv⟩

theorem count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : Coefficients, Q.c ≠ 0 → 0 < discriminant Q →
      normConstant Q ≠ 0 → height Q ≤ N ^ K → ∀ H : ℕ, H ≤ N ^ K →
      ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, value Q z.1 z.2 = 0 ∧ z.1.natAbs ≤ H ∧ z.2.natAbs ≤ H) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := SignedQuadraticCount.generalized_count_le_rpow_eventually (4 * K + 8) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN Q hc hΔ hδ hM H hH S hS
  let D := (discriminant Q).natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr hΔ.ne'
  have hDcast : (D : ℤ) = discriminant Q := Int.natAbs_of_nonneg hΔ.le
  obtain ⟨hDb, hδb, hu, hv⟩ := polynomial_budget Q N K H (by omega) hM hH
  have hb := hN₀ N (by omega) D (N ^ (4 * K + 8)) (normConstant Q) hD hδ hDb le_rfl hδb
    (S.image (transform Q)) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      have hh := hS z hz
      obtain ⟨hzu, hzv⟩ := transform_bounds Q H z hh.2.1 hh.2.2
      refine ⟨?_, hzu.trans hu, hzv.trans hv⟩
      rw [hDcast]
      exact zero_maps_to_norm Q z hh.1)
  simpa only [card_image_of_injective _ (transform_injective Q hc hΔ.ne')] using hb

theorem grid_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P ≤ 2 → P.natDegree = 2 →
      0 < discriminant (coefficients P) → normConstant (coefficients P) ≠ 0 →
      BivariateHeight.height P ≤ N ^ K → ∀ B : ℕ, B ≤ N ^ K →
        ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := count (K + 3) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN P hD hout hΔ hδ hM B hB
  have hheight : height (coefficients P) ≤ N ^ (K + 3) :=
    (height_coefficients P).trans ((Nat.mul_le_mul_left 6 hM).trans
      (constant_mul_power N (by omega) 6 3 K (by decide)))
  have hB' : B ≤ N ^ (K + 3) := hB.trans (Nat.pow_le_pow_right (by omega) (by omega))
  apply hN₀ N (by omega) (coefficients P) (outer_coefficient_ne_zero P hD hout) hΔ hδ hheight B hB'
    (PlaneCurvePointCount.grid P B)
  intro z hz
  have hh := (PlaneCurvePointCount.mem_grid P B z).mp hz
  have hx : z.1.natAbs ≤ B := by
    have hc : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
    exact_mod_cast hc
  have hy : z.2.natAbs ≤ B := by
    have hc : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
    exact_mod_cast hc
  refine ⟨?_, hx, hy⟩
  rw [← ConicPolynomialPresentation.evaluation, reconstruction P hD]
  exact hh.2.2

end PaperP1.PositiveDiscriminantConicCount
