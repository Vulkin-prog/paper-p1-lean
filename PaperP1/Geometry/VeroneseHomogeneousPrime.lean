module

public import PaperP1.Geometry.GradedVeroneseProj

/-! # Actual homogeneous projective primes correspond under the Veronese isomorphism -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.VeroneseHomogeneousPrime

open AlgebraicGeometry CategoryTheory

variable {F A : Type u} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)

def pointEquiv :
    letI := GradedVeroneseGrading.grading G D hD
    ProjectiveSpectrum G ≃ ProjectiveSpectrum (GradedVeroneseGrading.piece G D) := by
  letI := GradedVeroneseGrading.grading G D hD
  let e := GradedVeroneseProj.iso G D hD
  exact {
    toFun := e.hom
    invFun := e.inv
    left_inv := fun x ↦ Scheme.hom_inv_apply e x
    right_inv := fun x ↦ Scheme.inv_hom_apply e x }

theorem pointEquiv_apply :
    letI := GradedVeroneseGrading.grading G D hD
    ∀ p : ProjectiveSpectrum G, pointEquiv G D hD p = GradedVeroneseProj.map G D hD p := by
  let := GradedVeroneseGrading.grading G D hD
  intro p
  change (GradedVeroneseProj.iso G D hD).hom p = _
  rw [GradedVeroneseProj.iso_hom]


theorem comap_inverse :
    letI := GradedVeroneseGrading.grading G D hD
    ∀ p : ProjectiveSpectrum (GradedVeroneseGrading.piece G D),
      ((pointEquiv G D hD).symm p).asHomogeneousIdeal.toIdeal.comap
        (GradedVeroneseAlgebra.veronese G D).val.toRingHom = p.asHomogeneousIdeal.toIdeal := by
  let := GradedVeroneseGrading.grading G D hD
  intro p
  have he := (pointEquiv G D hD).apply_symm_apply p
  rw [pointEquiv_apply] at he
  exact congrArg (fun q : ProjectiveSpectrum (GradedVeroneseGrading.piece G D) ↦
    q.asHomogeneousIdeal.toIdeal) he

/-- Every actual nonirrelevant homogeneous Veronese prime is the contraction of an ordinary homogeneous prime. -/
theorem exists_prime_over :
    letI := GradedVeroneseGrading.grading G D hD
    ∀ p : ProjectiveSpectrum (GradedVeroneseGrading.piece G D),
      ∃ I : Ideal A, I.IsPrime ∧ I.IsHomogeneous G ∧
        I.comap (GradedVeroneseAlgebra.veronese G D).val.toRingHom = p.asHomogeneousIdeal.toIdeal := by
  let := GradedVeroneseGrading.grading G D hD
  intro p
  let q := (pointEquiv G D hD).symm p
  exact ⟨q.asHomogeneousIdeal.toIdeal, q.isPrime, q.asHomogeneousIdeal.isHomogeneous,
    comap_inverse G D hD p⟩

end PaperP1.VeroneseHomogeneousPrime
