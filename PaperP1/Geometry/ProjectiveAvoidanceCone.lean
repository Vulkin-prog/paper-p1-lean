module

public import PaperP1.Geometry.ProjectiveSectionFiniteSet

/-! # A projective section-avoiding form has no nonzero common zero on the affine cone -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveAvoidanceCone

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem linear_nonvanishing {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (havoid : ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f, eval p.rep ℓ ≠ 0)
    (w : σ → F) (hw : w ≠ 0) (hcurve : ∀ P ∈ I, eval w P = 0) (hfzero : eval w f = 0) :
    eval w ℓ ≠ 0 := by
  let p := Projectivization.mk F w hw
  have hp : p ∈ ProjectiveSectionFiniteSet.sectionLocus I f :=
    (ProjectiveSectionFiniteSet.mem_section_mk_iff I hI f hf w hw).mpr ⟨hcurve, hfzero⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
  change (fun i ↦ (a : F) * w i) = p.rep at ha
  intro hz
  apply havoid p hp
  rw [← ha, HomogeneousPolynomialEvaluation.eval_scale ℓ hℓ, hz, mul_zero]

theorem common_zero {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
    (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
    (havoid : ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f, eval p.rep ℓ ≠ 0)
    (w : σ → F) (hcurve : ∀ P ∈ I, eval w P = 0) (hfzero : eval w f = 0) (hℓzero : eval w ℓ = 0) :
    w = 0 := by
  by_contra hw
  exact linear_nonvanishing I hI f hf ℓ hℓ havoid w hw hcurve hfzero hℓzero

end PaperP1.ProjectiveAvoidanceCone
