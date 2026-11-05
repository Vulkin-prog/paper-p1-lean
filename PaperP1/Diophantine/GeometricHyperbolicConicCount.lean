module

public import PaperP1.Algebra.ConicIrreducibility
public import PaperP1.Diophantine.PositiveDiscriminantConicCount

/-! # The actual positive-discriminant geometric conic count in original coordinates

No non-degeneracy or leading-coordinate condition is supplied as an input.
The coefficient and point heights lie in any fixed polynomial ambient box.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricHyperbolicConicCount

open Polynomial Finset PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation
open PaperP1.ConicCoordinateChanges PaperP1.GeometricFactorSwap

theorem coefficient_height_budget (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2)
    (t : ℕ) (ht : t ≤ 2) :
    height (coefficients (BivariateLinearShear.shear (t : ℤ) P)) ≤ 54 * BivariateHeight.height P := by
  rw [coefficients_shear P hD]
  calc
    _ ≤ 9 * height (coefficients P) := height_shear t ht _
    _ ≤ 9 * (6 * BivariateHeight.height P) := Nat.mul_le_mul_left _ (height_coefficients P)
    _ = _ := by ring

theorem point_natAbs_bounds (t : ℕ) (ht : t ≤ 2) (B : ℕ) (z : ℤ × ℤ)
    (hx : z.1.natAbs ≤ B) (hy : z.2.natAbs ≤ B) :
    (IntegerPlaneShear.point (t : ℤ) z).1.natAbs ≤ 3 * B ∧
      (IntegerPlaneShear.point (t : ℤ) z).2.natAbs ≤ 3 * B := by
  change (z.1 - (t : ℤ) * z.2).natAbs ≤ 3 * B ∧ z.2.natAbs ≤ 3 * B
  have hh := Int.natAbs_sub_le z.1 ((t : ℤ) * z.2)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hh
  constructor
  · calc
      _ ≤ z.1.natAbs + t * z.2.natAbs := hh
      _ ≤ B + 2 * B := Nat.add_le_add hx (Nat.mul_le_mul ht hy)
      _ = _ := by omega
  · exact hy.trans (Nat.le_mul_of_pos_left B (by decide : 0 < (3 : ℕ)))

theorem count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 → Geometric P →
      0 < discriminant (coefficients P) → BivariateHeight.height P ≤ N ^ K →
      ∀ B : ℕ, B ≤ N ^ K → ((PlaneCurvePointCount.grid P B).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := PositiveDiscriminantConicCount.count (K + 6) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN P hD hgeo hΔ hM B hB
  have hne : P ≠ 0 := by intro hz; simp [PlaneCurvePointCount.degree, hz] at hD
  obtain ⟨t, ht, hout⟩ := BoundedPlaneShear.exists_full_outer_degree P hne
  rw [hD] at ht hout
  let R := BivariateLinearShear.shear (t : ℤ) P
  have hRdegree : PlaneCurvePointCount.degree R = 2 := (BivariateLinearShear.shear_degree _ P).trans hD
  have hRgeo : Geometric R := IntegerPlaneShear.geometric (t : ℤ) P hne hgeo
  have hRc : (coefficients R).c ≠ 0 := outer_coefficient_ne_zero R hRdegree.le hout
  have hRΔ : 0 < discriminant (coefficients R) := by
    dsimp only [R]
    rw [discriminant_shear P hD.le]
    exact hΔ
  have hRδ : normConstant (coefficients R) ≠ 0 :=
    ConicIrreducibility.grid_normConstant_ne_zero R hRdegree.le hout hRgeo
  have hRheight : height (coefficients R) ≤ N ^ (K + 6) :=
    (coefficient_height_budget P hD.le t ht).trans ((Nat.mul_le_mul_left 54 hM).trans
      (PositiveDiscriminantConicCount.constant_mul_power N (by omega) 54 6 K (by decide)))
  have hB' : 3 * B ≤ N ^ (K + 6) := by
    calc
      _ ≤ 3 * N ^ K := Nat.mul_le_mul_left _ hB
      _ ≤ N ^ (K + 2) := PositiveDiscriminantConicCount.constant_mul_power N (by omega) 3 2 K (by decide)
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  let S := PlaneCurvePointCount.grid P B
  let U := S.image (IntegerPlaneShear.point (t : ℤ))
  have hb := hN₀ N (by omega) (coefficients R) hRc hRΔ hRδ hRheight (3 * B) hB' U (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    have hh := (PlaneCurvePointCount.mem_grid P B z).mp hz
    have hx : z.1.natAbs ≤ B := by
      have hc : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
      exact_mod_cast hc
    have hy : z.2.natAbs ≤ B := by
      have hc : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
      exact_mod_cast hc
    obtain ⟨hu, hv⟩ := point_natAbs_bounds t ht B z hx hy
    refine ⟨?_, hu, hv⟩
    rw [← evaluation, reconstruction R hRdegree.le]
    exact IntegerPlaneShear.point_zero (t : ℤ) P z hh.2.2)
  have hcard : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
  simpa only [hcard] using hb

theorem natural_height_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = 2 → Geometric P →
      0 < discriminant (coefficients P) → BivariateHeight.height P ≤ N ^ K →
        ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := count (K + 1) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN P hD hgeo hΔ hM
  have hM' : BivariateHeight.height P ≤ N ^ (K + 1) :=
    hM.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hheight : N ≤ N ^ (K + 1) := by
    have hp : 0 < N ^ K := Nat.pow_pos (by omega)
    have hh := Nat.le_mul_of_pos_left N hp
    simpa only [pow_succ] using hh
  exact hN₀ N (by omega) P hD hgeo hΔ hM' N hheight

end PaperP1.GeometricHyperbolicConicCount
