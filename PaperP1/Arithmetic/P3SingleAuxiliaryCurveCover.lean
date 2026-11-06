module

public import PaperP1.Geometry.P3HypersurfaceAuxiliaryDegreeBudget
public import PaperP1.Arithmetic.PresentedCurveDegreeCutoff

/-! # One actual auxiliary equation gives bounded-degree curves and explicit integer-point exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3SingleAuxiliaryCurveCover

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cover_of_equation (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℚ)
    (hspan : I = Ideal.span {q}) (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q))
    (hq : q.IsHomogeneous d) (hdegree : q.totalDegree = d)
    (e : ℕ) (G : MvPolynomial (Fin 4) ℚ) (hG : G.IsHomogeneous e) (hnot : ¬ q ∣ G)
    (M N : ℕ) (hM : 0 < M) (hN : 1 ≤ N) (U : Finset (Fin 4 → ℤ))
    (hU : U ⊆ UniformP3HypersurfaceCover.points q N)
    (hzero : ∀ v ∈ U, eval (fun j ↦ (v j : ℚ)) G = 0) :
    letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI;
    ∃ (T : Finset (Fin 4 → ℤ))
      (family : Finset (GradedProjectiveCurveData.Curve (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I))),
      T ⊆ U ∧ (∀ Γ ∈ family, Γ.degree ≤ (M : ℚ)) ∧ family.card ≤ e * d ∧
      (T.card : ℝ) ≤ UniformIntegralCurveCount.constant.{0} 4 * ((e * d : ℕ) : ℝ) ^ 2 *
        (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (M : ℝ)) ∧
      ∀ v ∈ U, v ∉ T → ∃ Γ ∈ family,
        ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk I), eval (fun j ↦ (v j : ℚ)) P = 0 := by
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI
  obtain ⟨all, hcard, _hdegrees, hsum, hcover⟩ := P3HypersurfaceAuxiliaryDegreeBudget.exists_family
    I hI d q hspan hgeom hq hdegree e G hG hnot
  let f := HomogeneousQuotientGrading.mk (homogeneousSubmodule (Fin 4) ℚ) I
  have hscalar (a : ℚ) : f (algebraMap ℚ (MvPolynomial (Fin 4) ℚ) a) =
      algebraMap ℚ (MvPolynomial (Fin 4) ℚ ⧸ I) a := rfl
  have honto : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hsumR : (∑ Γ ∈ all, (Γ.degree : ℝ)) ≤ ((e * d : ℕ) : ℝ) := by exact_mod_cast hsum
  have hnormal (v : Fin 4 → ℤ) (hv : v ∈ U) : v 3 = 1 :=
    ((UniformP3HypersurfaceCover.mem_points q N v).mp (hU hv)).2.1
  have hheight (v : Fin 4 → ℤ) (hv : v ∈ U) : ∀ i, |v i| ≤ (N : ℤ) :=
    ((UniformP3HypersurfaceCover.mem_points q N v).mp (hU hv)).1
  have hcoverage (v : Fin 4 → ℤ) (hv : v ∈ U) : ∃ Γ ∈ all,
      ∀ P ∈ PresentedProjectiveCurveData.coordinateIdeal f Γ, eval (fun i ↦ (v i : ℚ)) P = 0 :=
    hcover N v (hU hv) (hzero v hv)
  obtain ⟨T, low, hTU, _hlow, hMlow, hlowCard, hTbound, hlowCover⟩ :=
    PresentedCurveDegreeCutoff.cover f hscalar honto all ((e * d : ℕ) : ℝ) hsumR M N hM hN 3 U
      hnormal hheight hcoverage
  refine ⟨T, low, hTU, hMlow, hlowCard.trans hcard, ?_, hlowCover⟩
  simpa only [Nat.card_fin] using hTbound

end PaperP1.P3SingleAuxiliaryCurveCover
