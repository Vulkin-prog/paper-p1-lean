module

public import PaperP1.Geometry.SourceEmbeddingCoordinateAlgebra
public import PaperP1.Algebra.GradedSurjectivePresentation

/-! # The actual homogeneous coordinate quotient of a curve in the chosen source embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveEmbeddingCoordinates

open PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] {ι : Type} (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))

abbrev SourceRing := HomogeneousSplitRadicalVeronese.veronese c D I J ⧸ P

local instance quotientRing : CommRing (SourceRing c D I J P) := inferInstance
local instance quotientSemiring : Semiring (SourceRing c D I J P) := (quotientRing c D I J P).toSemiring
local instance quotientModule : Module F (SourceRing c D I J P) := Algebra.toModule

def sourcePiece (n : ℕ) : Submodule F (SourceRing c D I J P) :=
  HomogeneousQuotientGrading.piece (SourceVeroneseGrading.sourcePiece c D I J) P n

def evaluation : MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F ι D) F →+*ᵍ
    sourcePiece c D I J P := by
  letI := sourceGrading c D I J hdeg hD
  exact (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.sourcePiece c D I J) P).comp
    (SourceProjectiveEmbedding.evaluation c D I J hdeg hD)

theorem evaluation_surjective : Function.Surjective (evaluation c D I J hdeg hD P) :=
  Ideal.Quotient.mk_surjective.comp (SourceProjectiveEmbedding.evaluation_surjective c D I J hdeg hD)

theorem evaluation_commutes (a : F) : evaluation c D I J hdeg hD P
    (algebraMap F (MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) a) =
      algebraMap F (SourceRing c D I J P) a := by
  change Ideal.Quotient.mk P
    (MvPolynomial.aeval (sourceGenerator c D I J)
      (algebraMap F (MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) a)) = _
  rw [AlgHom.commutes]
  rfl

def coordinateIdeal : Ideal (MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) :=
  P.comap (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom

theorem kernel_eq : RingHom.ker (evaluation c D I J hdeg hD P).toRingHom =
    coordinateIdeal c D I J hdeg hD P := by
  change RingHom.ker ((Ideal.Quotient.mk P).comp (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker]
  rfl

abbrev CoordinateRing := MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F ⧸
  coordinateIdeal c D I J hdeg hD P

def coordinatePiece (n : ℕ) : Submodule F (CoordinateRing c D I J hdeg hD P) :=
  HomogeneousQuotientGrading.piece
    (MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F ι D) F)
    (coordinateIdeal c D I J hdeg hD P) n

variable (hP : letI := sourceGrading c D I J hdeg hD
  P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))

include hP in
theorem coordinateIdeal_homogeneous :
    (coordinateIdeal c D I J hdeg hD P).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) := by
  let := sourceGrading c D I J hdeg hD
  exact (HomogeneousIdeal.comap (SourceProjectiveEmbedding.evaluation c D I J hdeg hD)
    (⟨P, hP⟩ : HomogeneousIdeal (SourceVeroneseGrading.sourcePiece c D I J))).isHomogeneous

def coordinateEquiv : CoordinateRing c D I J hdeg hD P ≃ₐ[F] SourceRing c D I J P := by
  exact (Ideal.quotientEquivAlgOfEq F (kernel_eq c D I J hdeg hD P).symm).trans
    (GradedSurjectivePresentation.toSource (evaluation c D I J hdeg hD P)
      (evaluation_commutes c D I J hdeg hD P) (evaluation_surjective c D I J hdeg hD P))

theorem coordinateEquiv_mk (a : MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) :
    coordinateEquiv c D I J hdeg hD P (Ideal.Quotient.mk _ a) = evaluation c D I J hdeg hD P a := by
  exact GradedSurjectivePresentation.toSource_mk (evaluation c D I J hdeg hD P)
    (evaluation_commutes c D I J hdeg hD P) (evaluation_surjective c D I J hdeg hD P) a

include hP in
theorem coordinateEquiv_piece_map (n : ℕ) :
    (coordinatePiece c D I J hdeg hD P n).map (coordinateEquiv c D I J hdeg hD P).toLinearMap =
      sourcePiece c D I J P n := by
  let := sourceGrading c D I J hdeg hD
  let : GradedAlgebra (sourcePiece c D I J P) :=
    HomogeneousQuotientGrading.grading (SourceVeroneseGrading.sourcePiece c D I J) P hP
  rw [coordinatePiece, HomogeneousQuotientGrading.piece, ← Submodule.map_comp]
  have he : (coordinateEquiv c D I J hdeg hD P).toLinearMap.comp
      (Ideal.Quotient.mkₐ F (coordinateIdeal c D I J hdeg hD P)).toLinearMap =
      (GradedSurjectivePresentation.algebraHom (evaluation c D I J hdeg hD P)
        (evaluation_commutes c D I J hdeg hD P)).toLinearMap := by
    apply LinearMap.ext
    intro a
    exact coordinateEquiv_mk c D I J hdeg hD P a
  rw [he]
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    exact (evaluation c D I J hdeg hD P).map_mem ha
  · intro y hy
    obtain ⟨a, ha, hay⟩ := GradedSurjectiveChartMap.homogeneous_preimage
      (evaluation c D I J hdeg hD P) (evaluation_surjective c D I J hdeg hD P) n y hy
    exact ⟨a, ha, hay⟩

def pieceEquiv (n : ℕ) : coordinatePiece c D I J hdeg hD P n ≃ₗ[F] sourcePiece c D I J P n :=
  (coordinateEquiv c D I J hdeg hD P).toLinearEquiv.ofSubmodules
    (coordinatePiece c D I J hdeg hD P n) (sourcePiece c D I J P n)
    (coordinateEquiv_piece_map c D I J hdeg hD P hP n)

include hP in
theorem piece_finrank (n : ℕ) : Module.finrank F (coordinatePiece c D I J hdeg hD P n) =
    Module.finrank F (sourcePiece c D I J P n) :=
  (pieceEquiv c D I J hdeg hD P hP n).finrank_eq

end PaperP1.SourceCurveEmbeddingCoordinates
