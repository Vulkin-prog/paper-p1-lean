module

public import PaperP1.Algebra.BivariateGraphSpecialization
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # The actual affine plane-curve coordinate domain, function field and generic coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineCurveFunctionField

open Polynomial

variable {F : Type*} [Field F]

def ideal (C₀ : F[X][X]) : Ideal F[X][X] := Ideal.span {C₀}

instance ideal_isPrime (C₀ : F[X][X]) [h : Fact (Irreducible C₀)] : (ideal C₀).IsPrime :=
  (Ideal.span_singleton_prime h.out.ne_zero).mpr h.out.prime

abbrev CoordinateRing (C₀ : F[X][X]) := F[X][X] ⧸ ideal C₀

abbrev FunctionField (C₀ : F[X][X]) := FractionRing (CoordinateRing C₀)

def specialize (C₀ : F[X][X]) [Fact (Irreducible C₀)] : F[X][X] →ₐ[F] FunctionField C₀ :=
  (IsScalarTower.toAlgHom F (CoordinateRing C₀) (FunctionField C₀)).comp (Ideal.Quotient.mkₐ F (ideal C₀))

def firstCoordinate (C₀ : F[X][X]) [Fact (Irreducible C₀)] : FunctionField C₀ := specialize C₀ (C X)

def secondCoordinate (C₀ : F[X][X]) [Fact (Irreducible C₀)] : FunctionField C₀ := specialize C₀ X

theorem specialize_zero_iff (C₀ : F[X][X]) [Fact (Irreducible C₀)] (P : F[X][X]) :
    specialize C₀ P = 0 ↔ C₀ ∣ P := by
  let : CommRing (CoordinateRing C₀) := inferInstance
  change (algebraMap (CoordinateRing C₀) (FunctionField C₀) (Ideal.Quotient.mk (ideal C₀) P) : FunctionField C₀) = 0 ↔ C₀ ∣ P
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton

theorem coordinates_evaluation (C₀ : F[X][X]) [Fact (Irreducible C₀)] :
    Polynomial.aevalAeval (R := F) (firstCoordinate C₀) (secondCoordinate C₀) = specialize C₀ := by
  ext <;> simp [firstCoordinate, secondCoordinate]

theorem coordinates_kernel (C₀ : F[X][X]) [Fact (Irreducible C₀)] :
    RingHom.ker (Polynomial.aevalAeval (R := F) (firstCoordinate C₀) (secondCoordinate C₀)).toRingHom = ideal C₀ := by
  rw [coordinates_evaluation]
  ext P
  exact (specialize_zero_iff C₀ P).trans Ideal.mem_span_singleton.symm

theorem first_transcendental (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree) :
    Transcendental F (firstCoordinate C₀) := by
  rw [transcendental_iff_injective, injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  have heq : specialize C₀ (C P) = aeval (firstCoordinate C₀) P := by
    rw [← coordinates_evaluation, Polynomial.aevalAeval_C]
  have hdvd : C₀ ∣ C P := (specialize_zero_iff C₀ _).mp (heq.trans hP)
  have hd := natDegree_le_of_dvd hdvd (C_ne_zero.mpr hne)
  rw [natDegree_C] at hd
  omega

theorem point_kernel_le (C₀ : F[X][X]) [Fact (Irreducible C₀)] (X Y : F)
    (hpoint : Polynomial.aevalAeval X Y C₀ = 0) :
    RingHom.ker (Polynomial.aevalAeval (R := F) (firstCoordinate C₀) (secondCoordinate C₀)).toRingHom ≤
      RingHom.ker (Polynomial.aevalAeval (R := F) X Y).toRingHom := by
  rw [coordinates_kernel, ideal, Ideal.span_singleton_le_iff_mem]
  exact hpoint

end PaperP1.AffineCurveFunctionField
