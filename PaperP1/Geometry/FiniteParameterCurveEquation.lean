module

public import PaperP1.Algebra.HomogeneousHeightOneEquation
public import PaperP1.Algebra.IntegralPrimeHeight
public import PaperP1.Algebra.GradedQuotientModuleGenerators
public import PaperP1.Algebra.GradedPolynomialGenerators
public import PaperP1.Algebra.GradedInjectiveHilbertComparison
public import PaperP1.Algebra.PlaneCurveHilbert
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! # A finite polynomial-parameter projection of an actual height-one curve has a plane equation of no larger genuine degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteParameterCurveEquation

open MvPolynomial

local instance polynomialRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

variable {F B : Type*} [Field F] [CommRing B] [IsDomain B] [Algebra F B]

theorem contracted_height (g : Fin 3 → B) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g)) (Q : Ideal B) [Q.IsPrime] :
    (Q.comap (aeval (R := F) g).toRingHom).height = Q.height := by
  let R := MvPolynomial (Fin 3) F
  let : Algebra R B := (aeval (R := F) g).toRingHom.toAlgebra
  let : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  let : Module.Finite R B := RingHom.finite_algebraMap.mp hfinite
  let : Algebra.IsIntegral R B := inferInstance
  exact (IntegralPrimeHeight.height_eq (R := R) Q).symm

theorem exists_equation
    (H : ℕ → Submodule F B) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 3 → B) (hg : ∀ i, g i ∈ H 1)
    (hfinite : (aeval (R := F) g).Finite) (hinj : Function.Injective (aeval (R := F) g))
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.IsHomogeneous H) (hheight : Q.height = 1)
    (E β : ℚ) (hcurve : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece H Q) (Polynomial.C E * Polynomial.X + Polynomial.C β)) :
    ∃ (e : ℕ) (h : MvPolynomial (Fin 3) F),
      0 < e ∧ h ≠ 0 ∧ h.IsHomogeneous e ∧
      Q.comap (aeval (R := F) g).toRingHom = Ideal.span {h} ∧ (e : ℚ) ≤ E := by
  let f := GradedPolynomialGenerators.gradedEval H g hg
  let P := Q.comap (aeval (R := F) g).toRingHom
  have hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin 3) F) :=
    GradedQuotientModuleGenerators.baseIdeal_homogeneous f Q hQ
  have hPheight : P.height = 1 := (contracted_height g hfinite hinj Q).trans hheight
  let : P.IsPrime := Ideal.IsPrime.comap (aeval (R := F) g).toRingHom
  obtain ⟨e, h, he, h0, hhom, heq⟩ := HomogeneousHeightOneEquation.exists_equation P hPhom hPheight
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3) F) P hPhom
  let := HomogeneousQuotientGrading.grading H Q hQ
  let (n : ℕ) : Module.Finite F (HomogeneousQuotientGrading.piece H Q n) :=
    HomogeneousQuotientGrading.piece_finite H Q n
  have hplane : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 3) F) P)
      (Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)) := by
    rw [heq]
    exact PlaneCurveHilbert.isHilbertPolynomial F h hhom h0
  have hscalar (a : F) : f (algebraMap F (MvPolynomial (Fin 3) F) a) = algebraMap F B a :=
    (aeval (R := F) g).commutes a
  have hle := GradedInjectiveHilbertComparison.linear_degree_le
    (GradedQuotientModuleGenerators.map f Q) (GradedQuotientModuleGenerators.map_commutes f hscalar Q)
    (GradedQuotientModuleGenerators.map_injective f Q) (e : ℚ) _ E β hplane hcurve
  exact ⟨e, h, he, h0, hhom, heq, hle⟩

end PaperP1.FiniteParameterCurveEquation
