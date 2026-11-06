module

public import PaperP1.Geometry.P3HypersurfaceRationalData
public import PaperP1.Geometry.ProjectiveHypersurfaceFiniteParameters
public import PaperP1.Geometry.GradedSurfaceSectionCurves
public import PaperP1.Algebra.HomogeneousGradientSection
public import PaperP1.Arithmetic.UniformP3HypersurfaceCover
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # One fixed actual curve family covers every normalized integer point with zero hypersurface gradient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HypersurfaceSingularCurves

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing : CommRing (MvPolynomial (Fin 4) ℚ) := inferInstance

theorem exists_family (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℚ)
    (hspan : I = Ideal.span {q}) (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q))
    (hq : q.IsHomogeneous d) (hdegree : q.totalDegree = d) :
    letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI;
    ∃ family : Finset (GradedProjectiveCurveData.Curve (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I)),
      family.card ≤ (d - 1) * d ∧ (∀ Γ ∈ family, Γ.degree ≤ (((d - 1) * d : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : Fin 4 → ℤ), v ∈ UniformP3HypersurfaceCover.points q H →
        (∀ i, eval (fun j ↦ (v j : ℚ)) (pderiv i q) = 0) → ∃ Γ ∈ family,
          ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk I), eval (fun j ↦ (v j : ℚ)) P = 0 := by
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI
  let : I.IsPrime := P3HypersurfaceRationalData.prime I q hspan hgeom
  let H := HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I
  let (n : ℕ) : Module.Finite ℚ (homogeneousSubmodule (Fin 4) ℚ n) := MvPolynomialHilbert.piece_finite ℚ (Fin 4) n
  let (n : ℕ) : Module.Finite ℚ (H n) := HomogeneousQuotientGrading.piece_finite (homogeneousSubmodule (Fin 4) ℚ) I n
  have hq0 : q ≠ 0 := (P3HypersurfaceRationalData.irreducible q hgeom).ne_zero
  have hd := P3HypersurfaceRationalData.degree_pos q hgeom d hdegree
  obtain ⟨g, hg, hfinite, hinj⟩ := ProjectiveHypersurfaceFiniteParameters.exists_parameters ℚ I hI d hd q hspan hq hq0
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial H (ProjectiveHypersurfaceHilbert.polynomial d) := by
    dsimp [H]
    rw [hspan]
    exact ProjectiveHypersurfaceHilbert.isHilbertPolynomial ℚ d q hq hq0
  obtain ⟨i, hf, hf0⟩ := HomogeneousGradientSection.exists_quotient_section I d hd q hspan hq hq0
  let f := Ideal.Quotient.mk I (pderiv i q)
  let b := Ideal.Quotient.mk I (X (3 : Fin 4))
  have hb : b ∈ H 1 := Submodule.mem_map.mpr ⟨_, isHomogeneous_X ℚ _, rfl⟩
  obtain ⟨family, hcard, hdegrees, hcover⟩ := GradedSurfaceSectionCurves.exists_family H g hg hfinite hinj
    (ProjectiveHypersurfaceHilbert.polynomial d) (ProjectiveHypersurfaceHilbert.natDegree_le d) hp d
    (ProjectiveHypersurfaceHilbert.coeff_two d) (d - 1) f hf hf0 b hb
  refine ⟨family, hcard, fun Γ hΓ ↦ (hdegrees Γ hΓ).2, ?_⟩
  intro R v hv hgrad
  have hv' := (UniformP3HypersurfaceCover.mem_points q R v).mp hv
  let φ := P3HypersurfaceRationalData.evaluation I q hspan (fun j ↦ (v j : ℚ)) hv'.2.2
  have hφf : φ f = 0 := hgrad i
  have hφb : φ b ≠ 0 := by
    change eval (fun j ↦ (v j : ℚ)) (X (3 : Fin 4)) ≠ 0
    rw [eval_X, hv'.2.1, Int.cast_one]
    exact one_ne_zero
  obtain ⟨Γ, hΓ, hΓφ⟩ := hcover φ hφf hφb
  refine ⟨Γ, hΓ, ?_⟩
  intro P hP
  have he := RingHom.mem_ker.mp (hΓφ hP)
  exact he

end PaperP1.P3HypersurfaceSingularCurves
