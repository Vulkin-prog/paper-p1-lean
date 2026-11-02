module

public import PaperP1.Algebra.CurveFormalBranch
public import PaperP1.Algebra.CurveFunctionField
public import PaperP1.Algebra.BivariateResultantNonzero

/-! # The actual curve function field embeds into the fraction field of a formal branch -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveSeriesField

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveFormalBranch PaperP1.CurveFunctionField

local instance : CommRing ℤ[X][X] := inferInstance
local instance (C₀ : ℤ[X][X]) : CommRing (CoordinateRing C₀) := inferInstance

theorem evaluation_zero_iff {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X])
    (hC : Irreducible C₀) (hy : 0 < degreeY C₀) (u : ℤ) (y : PowerSeries K)
    (hbranch : evaluation u y C₀ = 0) (P : ℤ[X][X]) : evaluation u y P = 0 ↔ C₀ ∣ P := by
  constructor
  · intro hz
    by_contra hn
    have hne := BivariateResultantNonzero.nonzero_of_not_dvd C₀ P hC hy hn
    obtain ⟨A, B, _hA, _hB, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant C₀ P le_rfl le_rfl
      (Or.inl (ne_of_gt hy))
    have h := congrArg (evaluation u y) hbez
    simp only [map_add, map_mul, hbranch, hz, zero_mul, zero_add, evaluation_C] at h
    apply hne
    apply coefficientLift_injective (K := K) u
    simpa only [map_zero] using h.symm
  · rintro ⟨Q, hQ⟩
    rw [hQ, map_mul, hbranch, zero_mul]

def coordinateMap {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X]) [hC : Fact (Irreducible C₀)]
    (hy : 0 < degreeY C₀) (u : ℤ) (y : PowerSeries K) (hbranch : evaluation u y C₀ = 0) :
    CoordinateRing C₀ →+* PowerSeries K :=
  Ideal.Quotient.lift (curveIdeal C₀) (evaluation u y) (fun P hP ↦
    (evaluation_zero_iff C₀ hC.out hy u y hbranch P).mpr (Ideal.mem_span_singleton.mp hP))

theorem coordinateMap_injective {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X]) [hC : Fact (Irreducible C₀)]
    (hy : 0 < degreeY C₀) (u : ℤ) (y : PowerSeries K) (hbranch : evaluation u y C₀ = 0) :
    Function.Injective (coordinateMap C₀ hy u y hbranch) := by
  intro a b h
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  have he : evaluation u y p = evaluation u y q := by
    simpa only [coordinateMap, Ideal.Quotient.lift_mk] using h
  have hz : evaluation u y (p - q) = 0 := by rw [map_sub, he, sub_self]
  exact Ideal.mem_span_singleton.mpr ((evaluation_zero_iff C₀ hC.out hy u y hbranch (p - q)).mp hz)

def fieldMap {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hy : 0 < degreeY C₀) (u : ℤ) (y : PowerSeries K) (hbranch : evaluation u y C₀ = 0) :
    FunctionField C₀ →+* FractionRing (PowerSeries K) :=
  IsFractionRing.map (coordinateMap_injective C₀ hy u y hbranch)

theorem fieldMap_specialize {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hy : 0 < degreeY C₀) (u : ℤ) (y : PowerSeries K) (hbranch : evaluation u y C₀ = 0) (P : ℤ[X][X]) :
    fieldMap C₀ hy u y hbranch (specialize C₀ P) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (evaluation u y P) := by
  simp [fieldMap, IsFractionRing.map, specialize, coordinateMap]

end PaperP1.CurveSeriesField
