module

public import PaperP1.Geometry.SourceProjectiveEmbedding
public import PaperP1.Algebra.GradedPolynomialPresentation
public import PaperP1.Algebra.SourceVeroneseHilbertPolynomial

/-! # The literal homogeneous coordinate algebra of the verified source embedding

The ideal is the kernel of the same polynomial map used to construct the
closed immersion. The graded pieces are the images of the ordinary polynomial
pieces in that quotient. Thus their computed Hilbert polynomial and multiplicity
refer to the actual chosen projective coordinate presentation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceEmbeddingCoordinateAlgebra

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

abbrev CoordinateRing {F : Type u} [Field F] {ι : Type} (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :=
  GradedPolynomialPresentation.CoordinateRing (F := F) (sourceGenerator c D I J)

def coordinatePiece {F : Type u} [Field F] {ι : Type} (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (n : ℕ) :
    Submodule F (CoordinateRing c D I J) := GradedPolynomialPresentation.piece (F := F) (sourceGenerator c D I J) n

section SourceGeneral

variable {F : Type u} [Field F] {ι : Type} (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)

theorem kernel_eq : RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom =
    GradedPolynomialPresentation.kernel (F := F) (sourceGenerator c D I J) := rfl

include hdeg hD in
theorem kernel_homogeneous :
    (GradedPolynomialPresentation.kernel (F := F) (sourceGenerator c D I J)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.kernel_homogeneous (sourcePiece c D I J)
    (sourceGenerator c D I J) (sourceGenerator_mem_one c D I J)

def coordinateEquiv : CoordinateRing c D I J ≃ₐ[F] HomogeneousSplitRadicalVeronese.veronese c D I J := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.toSource (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J)

theorem coordinateEquiv_mk (p : MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex F ι D) F) :
    coordinateEquiv c D I J hdeg hD (Ideal.Quotient.mk _ p) =
      SourceProjectiveEmbedding.evaluation c D I J hdeg hD p := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.toSource_mk (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J) p

@[instance_reducible] def coordinateGrading : GradedAlgebra (coordinatePiece c D I J) := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.grading (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J)

theorem coordinateEquiv_piece_map (n : ℕ) :
    (coordinatePiece c D I J n).map (coordinateEquiv c D I J hdeg hD).toLinearMap = sourcePiece c D I J n := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.piece_map (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J) n

def pieceEquiv (n : ℕ) : coordinatePiece c D I J n ≃ₗ[F] sourcePiece c D I J n := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialPresentation.pieceEquiv (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J) n

include hdeg hD in
theorem piece_finrank (n : ℕ) :
    Module.finrank F (coordinatePiece c D I J n) = Module.finrank F (sourcePiece c D I J n) :=
  (pieceEquiv c D I J hdeg hD n).finrank_eq

end SourceGeneral

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)

include hdeg hs hD in
theorem piece_finite (n : ℕ) : Module.Finite F (coordinatePiece c D I J n) := by
  have : Module.Finite F (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  exact Module.Finite.of_surjective (pieceEquiv c D I J hdeg hD n).symm.toLinearMap
    (pieceEquiv c D I J hdeg hD n).symm.surjective

include hs hD in
theorem isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial
    (coordinatePiece c D I J) (SourceVeroneseHilbertPolynomial.polynomial s c D I J hdeg) := by
  obtain ⟨N, hN⟩ := SourceVeroneseHilbertPolynomial.isHilbertPolynomial s c D I J hdeg hs hD
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [piece_finrank c D I J hdeg hD]
  exact hN n hn

include hdeg hs hD in
theorem exists_polynomial : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (coordinatePiece c D I J) p :=
  ⟨SourceVeroneseHilbertPolynomial.polynomial s c D I J hdeg, isHilbertPolynomial s c D I J hdeg hs hD⟩

theorem multiplicity : GradedHilbertPolynomial.multiplicity (coordinatePiece c D I J)
    (exists_polynomial s c D I J hdeg hs hD) = ((2 ^ s.length * D ^ 2 : ℕ) : ℚ) := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial s c D I J hdeg hs hD),
    SourceVeroneseHilbertPolynomial.natDegree s c D I J hdeg hD,
    SourceVeroneseHilbertPolynomial.leadingCoeff s c D I J hdeg hD]
  norm_num
  ring

theorem embedding_with_multiplicity :
    AlgebraicGeometry.IsClosedImmersion (SourceProjectiveEmbedding.embedding c D I J hdeg hD) ∧
      GradedHilbertPolynomial.multiplicity (coordinatePiece c D I J)
        (exists_polynomial s c D I J hdeg hs hD) = ((2 ^ s.length * D ^ 2 : ℕ) : ℚ) :=
  ⟨SourceProjectiveEmbedding.embedding_closedImmersion c D I J hdeg hD,
    multiplicity s c D I J hdeg hs hD⟩

end PaperP1.SourceEmbeddingCoordinateAlgebra
