module

public import PaperP1.Geometry.P3HypersurfaceSingularCurves

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
  let f := Ideal.Quotient.mk I G
  have hf : f ∈ H e := Submodule.mem_map.mpr ⟨G, hG, rfl⟩
  have hf0 : f ≠ 0 := by
    intro hz
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [hspan, Ideal.mem_span_singleton] at hm
    exact hnot hm
  let b := Ideal.Quotient.mk I (X (3 : Fin 4))
  have hb : b ∈ H 1 := Submodule.mem_map.mpr ⟨_, isHomogeneous_X ℚ _, rfl⟩
  obtain ⟨family, hcard, hdegrees, hcover⟩ := GradedSurfaceSectionCurves.exists_family H g hg hfinite hinj
    (ProjectiveHypersurfaceHilbert.polynomial d) (ProjectiveHypersurfaceHilbert.natDegree_le d) hp d
    (ProjectiveHypersurfaceHilbert.coeff_two d) e f hf hf0 b hb
  refine ⟨family, hcard, fun Γ hΓ ↦ (hdegrees Γ hΓ).2, ?_⟩
  intro R v hv hGzero
  have hv' := (UniformP3HypersurfaceCover.mem_points q R v).mp hv
  let φ := P3HypersurfaceRationalData.evaluation I q hspan (fun j ↦ (v j : ℚ)) hv'.2.2
  have hφf : φ f = 0 := hGzero
  have hφb : φ b ≠ 0 := by
    change eval (fun j ↦ (v j : ℚ)) (X (3 : Fin 4)) ≠ 0
    rw [eval_X, hv'.2.1, Int.cast_one]
    exact one_ne_zero
  obtain ⟨Γ, hΓ, hΓφ⟩ := hcover φ hφf hφb
  refine ⟨Γ, hΓ, ?_⟩
  intro P hP
  exact RingHom.mem_ker.mp (hΓφ hP)

end PaperP1.P3HypersurfaceAuxiliaryCurves
