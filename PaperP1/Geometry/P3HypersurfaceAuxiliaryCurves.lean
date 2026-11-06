module

public import PaperP1.Geometry.P3HypersurfaceAuxiliaryDegreeBudget

/-! # A literal auxiliary equation constructs actual bounded-degree P³ surface curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HypersurfaceAuxiliaryCurves

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_family (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℚ)
    (hspan : I = Ideal.span {q}) (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q))
    (hq : q.IsHomogeneous d) (hdegree : q.totalDegree = d)
    (e : ℕ) (G : MvPolynomial (Fin 4) ℚ) (hG : G.IsHomogeneous e) (hnot : ¬ q ∣ G) :
    letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI;
    ∃ family : Finset (GradedProjectiveCurveData.Curve (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I)),
      family.card ≤ e * d ∧ (∀ Γ ∈ family, Γ.degree ≤ (((e * d : ℕ) : ℚ))) ∧
      ∀ (H : ℕ) (v : Fin 4 → ℤ), v ∈ UniformP3HypersurfaceCover.points q H →
        eval (fun j ↦ (v j : ℚ)) G = 0 → ∃ Γ ∈ family,
          ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk I), eval (fun j ↦ (v j : ℚ)) P = 0 := by
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI
  obtain ⟨family, hcard, hdegrees, _hsum, hcover⟩ := P3HypersurfaceAuxiliaryDegreeBudget.exists_family
    I hI d q hspan hgeom hq hdegree e G hG hnot
  exact ⟨family, hcard, hdegrees, hcover⟩

end PaperP1.P3HypersurfaceAuxiliaryCurves
