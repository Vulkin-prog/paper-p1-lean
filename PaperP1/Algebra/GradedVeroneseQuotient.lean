module

public import PaperP1.Algebra.GradedVeroneseMap
public import PaperP1.Algebra.HomogeneousQuotientGrading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # The quotient of a literal Veronese by a contracted homogeneous ideal

The isomorphism with the Veronese of the actual quotient is proved together
with the identification of every rescaled homogeneous component.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseQuotient

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (I : Ideal A) (hI : I.IsHomogeneous G)
  (D : ℕ) (hD : 0 < D)

attribute [local instance] HomogeneousQuotientGrading.gradedMonoid

def contracted : Ideal (GradedVeroneseAlgebra.veronese G D) :=
  I.comap (GradedVeroneseAlgebra.veronese G D).val.toRingHom

abbrev Target := GradedVeroneseAlgebra.veronese (HomogeneousQuotientGrading.piece G I) D

def targetPiece (n : ℕ) : Submodule F (Target G I D) := by
  letI := HomogeneousQuotientGrading.grading G I hI
  exact GradedVeroneseGrading.piece (HomogeneousQuotientGrading.piece G I) D n

@[instance_reducible] def targetGrading : GradedAlgebra (targetPiece G I hI D) := by
  letI := HomogeneousQuotientGrading.grading G I hI
  exact GradedVeroneseGrading.grading (HomogeneousQuotientGrading.piece G I) D hD

def map : GradedVeroneseAlgebra.veronese G D →ₐ[F] Target G I D := by
  letI := HomogeneousQuotientGrading.grading G I hI
  exact GradedVeroneseMap.map G (HomogeneousQuotientGrading.piece G I)
    (HomogeneousQuotientGrading.mk G I) (HomogeneousQuotientGrading.mk_commutes G I) D

theorem map_val (x : GradedVeroneseAlgebra.veronese G D) :
    (map G I hI D x : A ⧸ I) = Ideal.Quotient.mk I (x : A) := rfl

include hD in
theorem map_surjective : Function.Surjective (map G I hI D) := by
  let := HomogeneousQuotientGrading.grading G I hI
  exact GradedVeroneseMap.surjective G (HomogeneousQuotientGrading.piece G I)
    (HomogeneousQuotientGrading.mk G I) (HomogeneousQuotientGrading.mk_commutes G I) D hD
    (HomogeneousQuotientGrading.mk_surjective G I)

theorem kernel_eq : RingHom.ker (map G I hI D) = contracted G I D := by
  ext x
  change map G I hI D x = 0 ↔ (x : A) ∈ I
  constructor
  · intro hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

def gradedMap : GradedVeroneseGrading.piece G D →+*ᵍ
    targetPiece G I hI D := by
  letI := HomogeneousQuotientGrading.grading G I hI
  exact GradedVeroneseMap.gradedMap G (HomogeneousQuotientGrading.piece G I)
    (HomogeneousQuotientGrading.mk G I) (HomogeneousQuotientGrading.mk_commutes G I) D

include hI hD in
theorem contracted_homogeneous :
    letI := GradedVeroneseGrading.grading G D hD
    (contracted G I D).IsHomogeneous (GradedVeroneseGrading.piece G D) := by
  let := GradedVeroneseGrading.grading G D hD
  let := HomogeneousQuotientGrading.grading G I hI
  let := targetGrading G I hI D hD
  have hk := ((⊥ : HomogeneousIdeal (targetPiece G I hI D)).comap
    (gradedMap G I hI D)).isHomogeneous
  change (RingHom.ker (map G I hI D)).IsHomogeneous (GradedVeroneseGrading.piece G D) at hk
  rw [kernel_eq] at hk
  exact hk

def equiv : (GradedVeroneseAlgebra.veronese G D ⧸ contracted G I D) ≃ₐ[F] Target G I D :=
  (Ideal.quotientEquivAlgOfEq F (kernel_eq G I hI D).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (map_surjective G I hI D hD))

theorem equiv_mk (x : GradedVeroneseAlgebra.veronese G D) :
    equiv G I hI D hD (Ideal.Quotient.mk (contracted G I D) x) = map G I hI D x := rfl

def piece (n : ℕ) : Submodule F (GradedVeroneseAlgebra.veronese G D ⧸ contracted G I D) :=
  HomogeneousQuotientGrading.piece (GradedVeroneseGrading.piece G D) (contracted G I D) n

theorem piece_map (n : ℕ) : (piece G I D n).map (equiv G I hI D hD).toLinearMap =
    targetPiece G I hI D n := by
  let := GradedVeroneseGrading.grading G D hD
  let := HomogeneousQuotientGrading.grading G I hI
  let := targetGrading G I hI D hD
  rw [piece, HomogeneousQuotientGrading.piece, ← Submodule.map_comp]
  have he : (equiv G I hI D hD).toLinearMap.comp
      (Ideal.Quotient.mkₐ F (contracted G I D)).toLinearMap = (map G I hI D).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact equiv_mk G I hI D hD x
  rw [he]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (gradedMap G I hI D).map_mem hx
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := GradedSurjectiveChartMap.homogeneous_preimage
      (gradedMap G I hI D) (map_surjective G I hI D hD) n y hy
    exact ⟨x, hx, hxy⟩

def pieceEquiv (n : ℕ) : piece G I D n ≃ₗ[F]
    targetPiece G I hI D n :=
  (equiv G I hI D hD).toLinearEquiv.ofSubmodules _ _ (piece_map G I hI D hD n)

include hD in
theorem finrank_eq (n : ℕ) : Module.finrank F (piece G I D n) =
    Module.finrank F (targetPiece G I hI D n) :=
  (pieceEquiv G I hI D hD n).finrank_eq

end PaperP1.GradedVeroneseQuotient
