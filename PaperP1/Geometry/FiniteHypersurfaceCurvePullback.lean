module

public import PaperP1.Geometry.FiniteParameterCurveEquation
public import PaperP1.Geometry.LinearHypersurfaceImage

/-! # An actual height-one curve on the finite hypersurface image pulls back into one nonzero source equation of no larger degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteHypersurfaceCurvePullback

open MvPolynomial LinearHypersurfaceImage

variable {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
  (H : ℕ → Submodule F A) [GradedAlgebra H]
  (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
  (hfinite : (aeval (R := F) g).Finite) (hinj : Function.Injective (aeval (R := F) g))

include hfinite hinj

theorem exists_equation (Q : Ideal (CoordinateRing (F := F) g y)) [Q.IsPrime]
    (hQ : letI := grading H g hg y hy; Q.IsHomogeneous (piece (F := F) g y))
    (hheight : Q.height = 1) (E β : ℚ)
    (hcurve : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (piece (F := F) g y) Q)
      (Polynomial.C E * Polynomial.X + Polynomial.C β)) :
    ∃ (e : ℕ) (h : MvPolynomial (Fin 3) F), 0 < e ∧ h ≠ 0 ∧ h.IsHomogeneous e ∧ (e : ℚ) ≤ E ∧
      aeval (R := F) g h ≠ 0 ∧ aeval (R := F) g h ∈ H e ∧ parameterMap (F := F) g y h ∈ Q := by
  let : (ideal (F := F) g y).IsPrime := ideal_prime g y
  let := grading H g hg y hy
  let (n : ℕ) : Module.Finite F (piece (F := F) g y n) := piece_finite g y n
  obtain ⟨e, h, he, h0, hhom, heq, hle⟩ := FiniteParameterCurveEquation.exists_equation
    (piece (F := F) g y)
    (fun i ↦ Ideal.Quotient.mk (ideal (F := F) g y) (X i.succ))
    (fun i ↦ by rw [← parameterMap_X]; exact parameter_mem g y i)
    (parameterMap_finite g y hfinite) (parameterMap_injective g y hinj) Q hQ hheight E β hcurve
  refine ⟨e, h, he, h0, hhom, hle, ?_, GradedPolynomialGenerators.eval_homogeneous H g hg e h hhom, ?_⟩
  · intro hz
    apply h0
    apply hinj
    simpa only [map_zero] using hz
  · have hm : h ∈ Ideal.span {h} := Ideal.mem_span_singleton_self h
    rw [← heq] at hm
    exact hm

end PaperP1.FiniteHypersurfaceCurvePullback
