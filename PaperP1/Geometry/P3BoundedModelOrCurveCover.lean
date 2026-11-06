module

public import PaperP1.Geometry.P3HypersurfaceAuxiliaryCurves
public import PaperP1.Algebra.P3HeightControlledEquation

/-! # Actual bounded integer surface models or a fixed bounded curve cover of the original population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3BoundedModelOrCurveCover

open MvPolynomial P3HomogeneousCoefficientFamily

attribute [local instance] MvPolynomial.gradedAlgebra

theorem model_or_cover (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℚ)
    (hspan : I = Ideal.span {q}) (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q))
    (hq : q.IsHomogeneous d) (hdegree : q.totalDegree = d) (H : ℕ) (hH : 1 ≤ H)
    (U : Finset (Fin 4 → ℤ)) (hU : U ⊆ UniformP3HypersurfaceCover.points q H) :
    letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI;
    ∃ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous d ∧ Q ≠ 0 ∧
      (∀ m, |Q.coeff m| ≤ (((3 * Fintype.card (Index d) * H ^ d) ^
        (Fintype.card (Index d) - 1) : ℕ) : ℤ)) ∧ (∀ v ∈ U, eval v Q = 0) ∧
      ((∃ c : ℚ, c ≠ 0 ∧ map (Int.castRingHom ℚ) Q = C c * q) ∨
        ∃ family : Finset (GradedProjectiveCurveData.Curve (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I)),
          family.card ≤ d * d ∧ (∀ Γ ∈ family, Γ.degree ≤ (((d * d : ℕ) : ℚ))) ∧
          ∀ v ∈ U, ∃ Γ ∈ family,
            ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk I), eval (fun j ↦ (v j : ℚ)) P = 0) := by
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI
  have hq0 : q ≠ 0 := (P3HypersurfaceRationalData.irreducible q hgeom).ne_zero
  have hheight (v : Fin 4 → ℤ) (hv : v ∈ U) : ∀ i, |v i| ≤ (H : ℤ) :=
    ((UniformP3HypersurfaceCover.mem_points q H v).mp (hU hv)).1
  have hroots (v : Fin 4 → ℤ) (hv : v ∈ U) : eval (fun k ↦ (v k : ℚ)) q = 0 :=
    ((UniformP3HypersurfaceCover.mem_points q H v).mp (hU hv)).2.2
  obtain ⟨Q, hQ, hQ0, hbound, hzero, hor⟩ := P3HeightControlledEquation.exists_model_or_auxiliary
    d H hH U hheight q hq hq0 hroots
  refine ⟨Q, hQ, hQ0, hbound, hzero, ?_⟩
  rcases hor with hnot | hmodel
  · apply Or.inr
    obtain ⟨family, hcard, hdegrees, hcover⟩ := P3HypersurfaceAuxiliaryCurves.exists_family
      I hI d q hspan hgeom hq hdegree d (map (Int.castRingHom ℚ) Q) (hQ.map _) hnot
    refine ⟨family, hcard, hdegrees, ?_⟩
    intro v hv
    apply hcover H v (hU hv)
    rw [P3HeightControlledEquation.integer_evaluation, hzero v hv, Int.cast_zero]
  · exact Or.inl hmodel

end PaperP1.P3BoundedModelOrCurveCover
