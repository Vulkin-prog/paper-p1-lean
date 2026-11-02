module

public import PaperP1.Algebra.CurveFibreRegularity
public import PaperP1.Algebra.PowerSeriesHenselLift

/-! # An actual formal branch at every root of a regular integer fibre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveFormalBranch

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFibreRegularity

def xSeries {K : Type*} [Field K] (u : ℤ) : PowerSeries K :=
  PowerSeries.X + PowerSeries.C (-(u : K))

def coefficientLift {K : Type*} [Field K] (u : ℤ) : ℤ[X] →+* PowerSeries K :=
  Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries K)) (xSeries u)

def curvePolynomial {K : Type*} [Field K] (P : ℤ[X][X]) (u : ℤ) : (PowerSeries K)[X] :=
  P.map (coefficientLift u)

def evaluation {K : Type*} [Field K] (u : ℤ) (y : PowerSeries K) : ℤ[X][X] →+* PowerSeries K :=
  Polynomial.eval₂RingHom (coefficientLift u) y

theorem coefficientLift_constant {K : Type*} [Field K] (u : ℤ) :
    PowerSeries.constantCoeff.comp (coefficientLift (K := K) u) = coefficientSpecialization u := by
  ext <;> simp [coefficientLift, xSeries, coefficientSpecialization]

theorem curvePolynomial_constant {K : Type*} [Field K] (P : ℤ[X][X]) (u : ℤ) :
    (curvePolynomial (K := K) P u).map PowerSeries.constantCoeff = fibre P u := by
  rw [curvePolynomial, Polynomial.map_map, coefficientLift_constant]
  rfl

theorem evaluation_eq {K : Type*} [Field K] (P : ℤ[X][X]) (u : ℤ) (y : PowerSeries K) :
    evaluation u y P = (curvePolynomial P u).eval y := Polynomial.eval₂_eq_eval_map (coefficientLift u)

theorem evaluation_C {K : Type*} [Field K] (u : ℤ) (y : PowerSeries K) (p : ℤ[X]) :
    evaluation u y (C p) = coefficientLift u p := by
  change Polynomial.eval₂ (coefficientLift u) y (C p) = _
  rw [Polynomial.eval₂_C]

theorem evaluation_Y {K : Type*} [Field K] (u : ℤ) (y : PowerSeries K) :
    evaluation u y (X : ℤ[X][X]) = y := by
  change Polynomial.eval₂ (coefficientLift u) y (X : ℤ[X][X]) = _
  rw [Polynomial.eval₂_X]

theorem curvePolynomial_leadingCoeff_unit {K : Type*} [Field K] [CharZero K]
    (P : ℤ[X][X]) (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) :
    IsUnit (curvePolynomial (K := K) P u).leadingCoeff := by
  have hl := ((regular_iff P hP hy u).mp hu).1
  have hlK : coefficientSpecialization (K := K) u P.leadingCoeff ≠ 0 := by
    change ((P.leadingCoeff.eval (-u) : ℤ) : K) ≠ 0
    exact_mod_cast hl
  have hc : PowerSeries.constantCoeff (coefficientLift (K := K) u P.leadingCoeff) =
      coefficientSpecialization u P.leadingCoeff :=
    congrArg (fun φ : ℤ[X] →+* K ↦ φ P.leadingCoeff) (coefficientLift_constant u)
  have hunit : IsUnit (coefficientLift (K := K) u P.leadingCoeff) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hc]
    exact isUnit_iff_ne_zero.mpr hlK
  have hleading : (curvePolynomial (K := K) P u).leadingCoeff = coefficientLift u P.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hunit.ne_zero
  rwa [hleading]

theorem exists_branch {K : Type*} [Field K] [CharZero K] (P : ℤ[X][X]) (hP : Irreducible P)
    (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) (z : K) (hz : (fibre P u).eval z = 0) :
    ∃ y : PowerSeries K, PowerSeries.constantCoeff y = z ∧ evaluation u y P = 0 := by
  have hroot : ((curvePolynomial P u).map PowerSeries.constantCoeff).eval z = 0 := by
    rwa [curvePolynomial_constant]
  have hderiv : ((curvePolynomial P u).map PowerSeries.constantCoeff).derivative.eval z ≠ 0 := by
    rw [curvePolynomial_constant]
    exact root_derivative_ne_zero P hP hy u hu z hz
  obtain ⟨y, heval, hconstant⟩ := PowerSeriesHenselLift.exists_root (curvePolynomial P u)
    (curvePolynomial_leadingCoeff_unit P hP hy u hu) z hroot hderiv
  exact ⟨y, hconstant, (evaluation_eq P u y).trans heval⟩

theorem evaluation_first_factor {K : Type*} [Field K] (u i : ℤ) (y : PowerSeries K) :
    evaluation u y (C (X + C i)) = xSeries u + (i : PowerSeries K) := by
  change Polynomial.eval₂ (coefficientLift u) y (C (X + C i)) = _
  rw [Polynomial.eval₂_C, map_add]
  simp [coefficientLift]

theorem evaluation_selected_factor {K : Type*} [Field K] (u : ℤ) (y : PowerSeries K) :
    evaluation u y (C (X + C u)) = PowerSeries.X := by
  rw [evaluation_first_factor]
  simp [xSeries]

theorem evaluation_second_factor {K : Type*} [Field K] (u j : ℤ) (y : PowerSeries K) :
    evaluation u y (X + C (C j)) = y + (j : PowerSeries K) := by
  change Polynomial.eval₂ (coefficientLift u) y (X + C (C j)) = _
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp [coefficientLift]

theorem coefficientLift_injective {K : Type*} [Field K] [CharZero K] (u : ℤ) :
    Function.Injective (coefficientLift (K := K) u) := by
  have he : coefficientLift (K := K) u =
      (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K).comp
        ((Polynomial.taylorEquiv (-(u : K))).toRingHom.comp (Polynomial.mapRingHom (Int.castRingHom K))) := by
    ext1
    · exact Subsingleton.elim _ _
    · simp [coefficientLift, xSeries, Polynomial.taylorEquiv, Polynomial.taylor_X]
      exact (map_intCast (Polynomial.coeToPowerSeries.ringHom : K[X] →+* PowerSeries K) u).symm
  rw [he]
  exact (Polynomial.coe_injective K).comp ((Polynomial.taylorEquiv (-(u : K))).injective.comp
    (Polynomial.map_injective (Int.castRingHom K) Int.cast_injective))

end PaperP1.CurveFormalBranch
