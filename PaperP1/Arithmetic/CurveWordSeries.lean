module

public import PaperP1.Algebra.CurveFormalBranch
public import PaperP1.Algebra.PowerSeriesSquareGap
public import PaperP1.Algebra.FormalWordPolynomials

/-! # A selected unmatched regular fibre gives an actual simple zero in the word series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveWordSeries

open Polynomial Finset PaperP1.CurveFormalBranch PaperP1.FormalWordPolynomials

theorem word_value {K : Type*} [Field K] (I J : Finset ℤ) (u : ℤ) (y : PowerSeries K) :
    evaluation u y (wordOver ℤ I J) =
      (∏ i ∈ I, (xSeries u + (i : PowerSeries K))) * ∏ j ∈ J, (y + (j : PowerSeries K)) := by
  have hI : C (linearOver ℤ I) = ∏ i ∈ I, C (X + C i) := by
    simp only [linearOver, map_prod, Int.cast_id]
  have hJ : (linearOver ℤ J).map C = ∏ j ∈ J, (X + C (C j)) := by
    simp only [linearOver, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, map_C, Int.cast_id]
  rw [wordOver, hI, hJ, map_mul, map_prod, map_prod]
  simp only [evaluation_first_factor, evaluation_second_factor]

theorem first_factor_unit {K : Type*} [Field K] [CharZero K] (u i : ℤ) (hne : i ≠ u) :
    IsUnit (xSeries (K := K) u + (i : PowerSeries K)) := by
  have hcast : ((i - u : ℤ) : K) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hne)
  have hc : PowerSeries.constantCoeff (xSeries (K := K) u + (i : PowerSeries K)) = ((i - u : ℤ) : K) := by
    simp only [xSeries, map_add, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, map_intCast,
      zero_add, Int.cast_sub]
    ring
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [hc]
  exact isUnit_iff_ne_zero.mpr hcast

theorem second_factor_unit {K : Type*} [Field K] (y : PowerSeries K) (z : K)
    (hz : PowerSeries.constantCoeff y = z) (j : ℤ) (hne : z ≠ -(j : K)) :
    IsUnit (y + (j : PowerSeries K)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply isUnit_iff_ne_zero.mpr
  rw [map_add, hz, map_intCast]
  intro hzero
  apply hne
  exact add_right_cancel (hzero.trans (neg_add_cancel (j : K)).symm)

theorem exists_simple_factor {K : Type*} [Field K] [CharZero K] (I J : Finset ℤ)
    (u : ℤ) (hu : u ∈ I) (y : PowerSeries K) (z : K) (hz : PowerSeries.constantCoeff y = z)
    (hmismatch : ∀ j ∈ J, z ≠ -(j : K)) :
    ∃ v : PowerSeries K, IsUnit v ∧ evaluation u y (wordOver ℤ I J) = PowerSeries.X * v := by
  let v : PowerSeries K := (∏ i ∈ I.erase u, (xSeries u + (i : PowerSeries K))) *
    ∏ j ∈ J, (y + (j : PowerSeries K))
  have hfirst : IsUnit (∏ i ∈ I.erase u, (xSeries (K := K) u + (i : PowerSeries K))) :=
    IsUnit.prod_iff.mpr (fun i hi ↦ first_factor_unit u i (mem_erase.mp hi).1)
  have hsecond : IsUnit (∏ j ∈ J, (y + (j : PowerSeries K))) :=
    IsUnit.prod_iff.mpr (fun j hj ↦ second_factor_unit y z hz j (hmismatch j hj))
  refine ⟨v, hfirst.mul hsecond, ?_⟩
  have hs : xSeries u + (u : PowerSeries K) = PowerSeries.X := by
    simpa only [evaluation_first_factor] using evaluation_selected_factor u y
  rw [word_value, ← mul_prod_erase I (fun i ↦ xSeries u + (i : PowerSeries K)) hu, hs]
  exact mul_assoc _ _ _

theorem not_fraction_square_word {K : Type*} [Field K] [CharZero K] (I J : Finset ℤ)
    (u : ℤ) (hu : u ∈ I) (y : PowerSeries K) (z : K) (hz : PowerSeries.constantCoeff y = z)
    (hmismatch : ∀ j ∈ J, z ≠ -(j : K)) :
    ¬ IsSquare (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (evaluation u y (wordOver ℤ I J))) := by
  obtain ⟨v, hv, he⟩ := exists_simple_factor I J u hu y z hz hmismatch
  rw [he]
  exact PowerSeriesSquareGap.not_fraction_square v hv

end PaperP1.CurveWordSeries
