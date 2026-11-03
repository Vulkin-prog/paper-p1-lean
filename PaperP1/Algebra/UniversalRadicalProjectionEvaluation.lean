module

public import PaperP1.Algebra.UniversalRadicalProjection
public import PaperP1.Algebra.TrivariatePolynomialEvaluation

/-! # The fixed universal polynomial evaluates to the literal three-variable image equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniversalRadicalProjectionEvaluation

open Polynomial PaperP1.TrivariatePolynomialEquiv PaperP1.UniversalRadicalProjection
  PaperP1.RadicalProjectionPolynomial

def coefficientLift (F : Type*) [CommRing F] : F[X][X] →+* MvPolynomial (Fin 3) F :=
  (threeEquiv F).symm.toRingHom.comp C

def substitution (F : Type*) [CommRing F] (s : List F[X][X]) : Option (Fin s.length) → MvPolynomial (Fin 3) F
  | none => MvPolynomial.X 0
  | some i => coefficientLift F (s.get i)

def evaluateUniversal (F : Type*) [CommRing F] (s : List F[X][X]) :
    MvPolynomial (Option (Fin s.length)) ℤ →+* MvPolynomial (Fin 3) F :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom F)) (substitution F s)

theorem coefficientLift_CC (F : Type*) [CommRing F] (c : F) :
    coefficientLift F (C (C c)) = MvPolynomial.C c := by
  apply (threeEquiv F).injective
  change threeEquiv F ((threeEquiv F).symm (C (C (C c)))) =
    threeEquiv F (algebraMap F (MvPolynomial (Fin 3) F) c)
  rw [AlgEquiv.apply_symm_apply, (threeEquiv F).commutes]
  rfl

theorem coefficientLift_X (F : Type*) [CommRing F] : coefficientLift F (X : F[X][X]) = MvPolynomial.X 1 := by
  apply (threeEquiv F).injective
  change threeEquiv F ((threeEquiv F).symm (C (X : F[X][X]))) = threeEquiv F (MvPolynomial.X 1)
  rw [AlgEquiv.apply_symm_apply, threeEquiv_X_one]

theorem coefficientLift_CX (F : Type*) [CommRing F] : coefficientLift F (C (X : F[X])) = MvPolynomial.X 2 := by
  apply (threeEquiv F).injective
  change threeEquiv F ((threeEquiv F).symm (C (C (X : F[X])))) = threeEquiv F (MvPolynomial.X 2)
  rw [AlgEquiv.apply_symm_apply, threeEquiv_X_two]

theorem threeEquiv_comp_evaluate (F : Type*) [CommRing F] (s : List F[X][X]) :
    (threeEquiv F).toRingHom.comp (evaluateUniversal F s) =
      (Polynomial.mapRingHom (specialization F[X][X] s)).comp
        (MvPolynomial.optionEquivLeft ℤ (Fin s.length)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro n
    change threeEquiv F ((MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom F))
      (substitution F s)) (MvPolynomial.C n)) =
        ((MvPolynomial.optionEquivLeft ℤ (Fin s.length)) (MvPolynomial.C n)).map (specialization F[X][X] s)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.optionEquivLeft_C, Polynomial.map_C]
    change threeEquiv F (algebraMap F (MvPolynomial (Fin 3) F) (n : F)) = _
    rw [(threeEquiv F).commutes]
    simp [specialization]
  · intro o
    cases o with
    | none =>
      change threeEquiv F ((MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom F))
        (substitution F s)) (MvPolynomial.X none)) =
        ((MvPolynomial.optionEquivLeft ℤ (Fin s.length)) (MvPolynomial.X none)).map (specialization F[X][X] s)
      rw [MvPolynomial.eval₂Hom_X']
      change threeEquiv F (MvPolynomial.X 0) = _
      rw [threeEquiv_X_zero, MvPolynomial.optionEquivLeft_X_none, Polynomial.map_X]
    | some i =>
      change threeEquiv F ((MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom F))
        (substitution F s)) (MvPolynomial.X (some i))) =
        ((MvPolynomial.optionEquivLeft ℤ (Fin s.length)) (MvPolynomial.X (some i))).map (specialization F[X][X] s)
      rw [MvPolynomial.eval₂Hom_X']
      change threeEquiv F (coefficientLift F (s.get i)) = _
      rw [MvPolynomial.optionEquivLeft_X_some, Polynomial.map_C, specialization_X]
      exact (threeEquiv F).apply_symm_apply (C (s.get i))

theorem evaluation_eq_specialization (F : Type*) [CommRing F] (s : List F[X][X]) :
    evaluateUniversal F s (universalPolynomial s.length) =
      asMvPolynomial F ((universalEquation s.length).map (specialization F[X][X] s)) := by
  apply (threeEquiv F).injective
  have hh := congrArg (fun φ : MvPolynomial (Option (Fin s.length)) ℤ →+* F[X][X][X] ↦
    φ (universalPolynomial s.length)) (threeEquiv_comp_evaluate F s)
  change threeEquiv F (evaluateUniversal F s (universalPolynomial s.length)) =
    ((MvPolynomial.optionEquivLeft ℤ (Fin s.length)) (universalPolynomial s.length)).map (specialization F[X][X] s) at hh
  simpa only [universalPolynomial, AlgEquiv.apply_symm_apply, asMvPolynomial] using hh

theorem evaluation_eq_equation (F K : Type*) [CommRing F] [IsDomain F] [Field K] [CharZero K]
    [Algebra F[X][X] K] [IsFractionRing F[X][X] K] (s : List F[X][X])
    (hs : PaperP1.IndependentQuadraticTower.Independent (s.map (algebraMap F[X][X] K))) :
    evaluateUniversal F s (universalPolynomial s.length) = asMvPolynomial F (equation F[X][X] s) := by
  rw [evaluation_eq_specialization, equation_specializes F[X][X] K s hs]

end PaperP1.UniversalRadicalProjectionEvaluation
