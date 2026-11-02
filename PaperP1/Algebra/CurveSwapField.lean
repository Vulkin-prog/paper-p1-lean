module

public import PaperP1.Algebra.CurveFunctionField
public import PaperP1.Algebra.FormalWordDegrees

/-! # Swapping the variables of the actual curve function field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveSwapField

open Polynomial PaperP1.CurveFunctionField PaperP1.FormalWordPolynomials

local instance : CommRing ℤ[X][X] := inferInstance
local instance (C₀ : ℤ[X][X]) : CommRing (CoordinateRing C₀) := inferInstance

theorem swap_dvd_iff (C₀ P : ℤ[X][X]) :
    Bivariate.swap C₀ ∣ Bivariate.swap P ↔ C₀ ∣ P := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Bivariate.swap Q, ?_⟩
    simpa only [map_mul, Bivariate.swap_swap_apply] using congrArg Bivariate.swap hQ
  · rintro ⟨Q, rfl⟩
    exact ⟨Bivariate.swap Q, map_mul Bivariate.swap C₀ Q⟩

def coordinateMap (C₀ : ℤ[X][X]) : CoordinateRing C₀ →+* CoordinateRing (Bivariate.swap C₀) :=
  Ideal.Quotient.lift (curveIdeal C₀)
    ((Ideal.Quotient.mk (curveIdeal (Bivariate.swap C₀))).comp Bivariate.swap.toRingHom)
    (fun P hP ↦ Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ((swap_dvd_iff C₀ P).mpr (Ideal.mem_span_singleton.mp hP))))

theorem coordinateMap_injective (C₀ : ℤ[X][X]) : Function.Injective (coordinateMap C₀) := by
  intro a b h
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  have he : Ideal.Quotient.mk (curveIdeal (Bivariate.swap C₀)) (Bivariate.swap p) =
      Ideal.Quotient.mk (curveIdeal (Bivariate.swap C₀)) (Bivariate.swap q) := by
    simpa [coordinateMap] using h
  apply Ideal.mem_span_singleton.mpr
  apply (swap_dvd_iff C₀ (p - q)).mp
  rw [map_sub]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)

def fieldMap (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] [Fact (Irreducible (Bivariate.swap C₀))] :
    FunctionField C₀ →+* FunctionField (Bivariate.swap C₀) :=
  IsFractionRing.map (coordinateMap_injective C₀)

theorem fieldMap_specialize (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    [Fact (Irreducible (Bivariate.swap C₀))] (P : ℤ[X][X]) :
    fieldMap C₀ (specialize C₀ P) = specialize (Bivariate.swap C₀) (Bivariate.swap P) := by
  simp [fieldMap, IsFractionRing.map, specialize, coordinateMap]

theorem square_word_swap (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    [Fact (Irreducible (Bivariate.swap C₀))] (I J : Finset ℤ)
    (h : IsSquare (specialize C₀ (wordOver ℤ I J))) :
    IsSquare (specialize (Bivariate.swap C₀) (wordOver ℤ J I)) := by
  have hs := h.map (fieldMap C₀)
  simpa only [fieldMap_specialize, FormalWordDegrees.word_swap] using hs

end PaperP1.CurveSwapField
