module

public import PaperP1.Diophantine.ParabolicConicFiniteCount
public import PaperP1.Diophantine.GeometricHyperbolicConicCount

/-! # Uniform parabolic conic counts at polynomial coefficient height

The geometric theorem chooses a bounded integer shear and proves the required
non-degeneracy internally. All original signs and axis points remain present.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricParabolicConicCount

open Polynomial Finset Filter ConicNormCoordinates ConicPolynomialPresentation
open ConicCoordinateChanges GeometricFactorSwap

theorem count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : Coefficients, Q.c ≠ 0 → discriminant Q = 0 →
      linear Q ≠ 0 → height Q ≤ N ^ K → ∀ H : ℕ, H ≤ 3 * N →
      ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, value Q z.1 z.2 = 0 ∧ |z.1| ≤ (H : ℤ)) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨Nd, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (2 * K + 3)
    (ε / 2) (by positivity)
  have ht := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (8 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 2 (max Nd Nc), ?_⟩
  intro N hN Q hcQ hΔ hβ hM H hH S hS
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hβb : (linear Q).natAbs ≤ N ^ (2 * K + 3) := by
    calc
      _ ≤ 6 * height Q ^ 2 := linear_bound Q
      _ ≤ 6 * (N ^ K) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM 2)
      _ = 6 * N ^ (2 * K) := by rw [← pow_mul, Nat.mul_comm K 2]
      _ ≤ _ := PositiveDiscriminantConicCount.constant_mul_power N (by omega) 6 3 (2 * K) (by decide)
  have hdiv := hd N (by omega) (linear Q).natAbs hβb
  have hconst := hc N (by omega)
  have htau : 8 * ((linear Q).natAbs.divisors.card : ℝ) ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul hconst hdiv (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hsN : 1 ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast (show 1 ≤ N by omega))
  have hsH : Real.sqrt (2 * (H : ℝ)) ≤ 3 * Real.sqrt (N : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    have hHr : (H : ℝ) ≤ 3 * N := by exact_mod_cast hH
    nlinarith
  have hroot : Real.sqrt (2 * (H : ℝ)) + 1 ≤ 4 * Real.sqrt (N : ℝ) := by linarith
  calc
    (S.card : ℝ) ≤ 2 * ((linear Q).natAbs.divisors.card : ℝ) *
        (Real.sqrt (2 * (H : ℝ)) + 1) := ParabolicConicFiniteCount.finite_count Q hcQ hΔ hβ H S hS
    _ ≤ 2 * ((linear Q).natAbs.divisors.card : ℝ) * (4 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (8 * ((linear Q).natAbs.divisors.card : ℝ)) * Real.sqrt (N : ℝ) := by ring
    _ ≤ (N : ℝ) ^ ε * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_right htau (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNp]; congr 1; ring

theorem natural_height_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 → Geometric P →
      discriminant (coefficients P) = 0 → BivariateHeight.height P ≤ N ^ K →
        ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := count (K + 6) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN P hD hgeo hΔ hM
  have hne : P ≠ 0 := by intro hz; simp [PlaneCurvePointCount.degree, hz] at hD
  obtain ⟨t, ht, hout⟩ := BoundedPlaneShear.exists_full_outer_degree P hne
  rw [hD] at ht hout
  let R := BivariateLinearShear.shear (t : ℤ) P
  have hRdegree : PlaneCurvePointCount.degree R = 2 := (BivariateLinearShear.shear_degree _ P).trans hD
  have hRgeo : Geometric R := IntegerPlaneShear.geometric (t : ℤ) P hne hgeo
  have hRc : (coefficients R).c ≠ 0 := outer_coefficient_ne_zero R hRdegree.le hout
  have hRΔ : discriminant (coefficients R) = 0 := by
    dsimp only [R]
    rw [discriminant_shear P hD.le]
    exact hΔ
  have hRδ := ConicIrreducibility.grid_normConstant_ne_zero R hRdegree.le hout hRgeo
  have hRβ : linear (coefficients R) ≠ 0 := by
    intro hz
    apply hRδ
    simp [normConstant, hRΔ, hz]
  have hRheight : height (coefficients R) ≤ N ^ (K + 6) :=
    (GeometricHyperbolicConicCount.coefficient_height_budget P hD.le t ht).trans
      ((Nat.mul_le_mul_left 54 hM).trans
        (PositiveDiscriminantConicCount.constant_mul_power N (by omega) 54 6 K (by decide)))
  let S := PlaneCurvePointCount.grid P N
  let U := S.image (IntegerPlaneShear.point (t : ℤ))
  have hb := hN₀ N (by omega) (coefficients R) hRc hRΔ hRβ hRheight (3 * N) le_rfl U (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hh := (PlaneCurvePointCount.mem_grid P N z).mp hz
    have hx : z.1.natAbs ≤ N := by
      have hc : (z.1.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
      exact_mod_cast hc
    have hy : z.2.natAbs ≤ N := by
      have hc : (z.2.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
      exact_mod_cast hc
    have hu := (GeometricHyperbolicConicCount.point_natAbs_bounds t ht N z hx hy).1
    refine ⟨?_, ?_⟩
    · rw [← evaluation, reconstruction R hRdegree.le]
      exact IntegerPlaneShear.point_zero (t : ℤ) P z hh.2.2
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hu)
  have hcard : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
  simpa only [hcard] using hb

end PaperP1.GeometricParabolicConicCount
