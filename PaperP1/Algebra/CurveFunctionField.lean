module

public import PaperP1.Algebra.BivariateDegrees
public import PaperP1.Algebra.FormalWordPolynomials
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Localization.FractionRing

/-! # The actual function field of an irreducible integer bivariate curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveFunctionField

open Polynomial PaperP1.BivariateDegrees PaperP1.FormalWordPolynomials

local instance : CommRing ℤ[X][X] := inferInstance

def curveIdeal (C₀ : ℤ[X][X]) : Ideal ℤ[X][X] := Ideal.span {C₀}

instance curveIdeal_isPrime (C₀ : ℤ[X][X]) [h : Fact (Irreducible C₀)] :
    (curveIdeal C₀).IsPrime :=
  (Ideal.span_singleton_prime h.out.ne_zero).mpr h.out.prime

abbrev CoordinateRing (C₀ : ℤ[X][X]) := ℤ[X][X] ⧸ curveIdeal C₀

abbrev FunctionField (C₀ : ℤ[X][X]) := FractionRing (CoordinateRing C₀)

def specialize (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] : ℤ[X][X] →+* FunctionField C₀ := by
  let : CommRing (CoordinateRing C₀) := inferInstance
  exact (algebraMap (CoordinateRing C₀) (FunctionField C₀)).comp (Ideal.Quotient.mk (curveIdeal C₀))

theorem specialize_zero_iff (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (P : ℤ[X][X]) :
    specialize C₀ P = 0 ↔ C₀ ∣ P := by
  unfold specialize
  rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton

theorem coordinate_charZero (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hdeg : 0 < degreeY C₀) :
    CharZero (CoordinateRing C₀) := by
  apply charZero_of_inj_zero
  intro n hn
  by_contra hne
  have hmem : (n : ℤ[X][X]) ∈ curveIdeal C₀ :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hn)
  have hdiv : C₀ ∣ (n : ℤ[X][X]) := Ideal.mem_span_singleton.mp hmem
  have hd := Polynomial.natDegree_le_of_dvd hdiv (Nat.cast_ne_zero.mpr hne)
  simp only [natDegree_natCast] at hd
  change 0 < C₀.natDegree at hdeg
  omega

theorem functionField_charZero (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hdeg : 0 < degreeY C₀) :
    CharZero (FunctionField C₀) := by
  let : CharZero (CoordinateRing C₀) := coordinate_charZero C₀ hdeg
  exact charZero_of_injective_algebraMap (IsFractionRing.injective (CoordinateRing C₀) (FunctionField C₀))

theorem first_linear_ne_zero (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdeg : 0 < degreeY C₀) (i : ℤ) : specialize C₀ (C (X + C i)) ≠ 0 := by
  intro hz
  have hdiv := (specialize_zero_iff C₀ _).mp hz
  have hp : (C (X + C i) : ℤ[X][X]) ≠ 0 := C_ne_zero.mpr (X_add_C_ne_zero i)
  have hd := Polynomial.natDegree_le_of_dvd hdiv hp
  simp only [natDegree_C] at hd
  change 0 < C₀.natDegree at hdeg
  omega

theorem second_linear_ne_zero (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdeg : 0 < degreeX C₀) (i : ℤ) : specialize C₀ (X + C (C i)) ≠ 0 := by
  intro hz
  obtain ⟨D, hD⟩ := (specialize_zero_iff C₀ _).mp hz
  have hp : (X + C (C i) : ℤ[X][X]) ≠ 0 := X_add_C_ne_zero (C i)
  have hprod : C₀ * D ≠ 0 := by rwa [← hD]
  have hd := factor_degreeX_le C₀ D hprod
  rw [← hD] at hd
  have hzero : degreeX (X + C (C i)) = 0 := by
    unfold degreeX
    rw [map_add, Bivariate.swap_Y, Bivariate.swap_C_C, ← C_add, natDegree_C]
  rw [hzero] at hd
  omega

theorem word_ne_zero (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
    (hdx : 0 < degreeX C₀) (hdy : 0 < degreeY C₀) (I J : Finset ℤ) :
    specialize C₀ (wordOver ℤ I J) ≠ 0 := by
  simp only [wordOver, linearOver, map_mul, map_prod, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_X, map_C]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ first_linear_ne_zero C₀ hdy i))
    (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ second_linear_ne_zero C₀ hdx j))

end PaperP1.CurveFunctionField
