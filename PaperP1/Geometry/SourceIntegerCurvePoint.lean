module

public import PaperP1.Arithmetic.SourceIntegerPointHeight
public import PaperP1.Geometry.OrdinaryCurveHostImage
public import PaperP1.Geometry.SourceProjectiveCurveLowDegreeExclusion
public import PaperP1.Geometry.SourceProjectiveCurveEmbeddingHilbert

/-! # Actual embedded integer-root point containment supplies the source host and embedded curve degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerCurvePoint

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeronese PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SplitRadicalPointHeight

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance nativeRing : CommRing (MvPolynomial (Fin 3) ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (d : Fin s.length → ℤ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (d i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (x y : ℤ) (w : Fin s.length → ℤ)
  (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y)

theorem base_evaluation (a : Base ℚ D) :
    WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot
      (SourceVeroneseGradedBaseMap.gradedBaseMap s (fun i : Fin s.length ↦ (d i : ℚ)) D hD I J hs a) =
      AffineLineClassification.valueMap (x : ℚ) (y : ℚ) (NativeVeroneseAffineIdeal.affineMap ℚ D a) := by
  change WeightedRootEvaluation.quotientEvaluation d D I J x y w hroot
    (HomogeneousSplitRadicalBaseInjection.basePolynomialMap (fun i : Fin s.length ↦ (d i : ℚ)) D I J (a : MvPolynomial (Fin 3) ℚ)) = _
  change WeightedRootEvaluation.quotientEvaluation d D I J x y w hroot
    (HomogeneousSplitRadicalFiniteVeronese.quotientMap (fun i : Fin s.length ↦ (d i : ℚ)) D I J (MvPolynomial.rename Sum.inl (a : MvPolynomial (Fin 3) ℚ))) = _
  rw [WeightedRootEvaluation.quotientEvaluation_mk]
  exact OrdinaryCurveHostImage.base_evaluation (OrdinaryIntegerPoints.evaluation (OrdinaryIntegerPoints.lift x y w))
    (x : ℚ) (y : ℚ) (by rw [OrdinaryIntegerPoints.evaluation_X]; rfl)
    (by rw [OrdinaryIntegerPoints.evaluation_X]; rfl)
    (by rw [OrdinaryIntegerPoints.evaluation_X, OrdinaryIntegerPoints.lift_Z, Int.cast_one]) a.val

theorem host_image (P : Ideal (veronese (fun i : Fin s.length ↦ (d i : ℚ)) D I J))
    (hcurve : P ≤ RingHom.ker (WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot)) :
    NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hD P) ≤
      RingHom.ker (AffineLineClassification.valueMap (x : ℚ) (y : ℚ)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change AffineLineClassification.valueMap (x : ℚ) (y : ℚ) (NativeVeroneseAffineIdeal.affineMap ℚ D a) = 0
  exact (base_evaluation s d D I J hs hD x y w hroot a).symm.trans (RingHom.mem_ker.mp (hcurve ha))

theorem containment_iff (P : Ideal (veronese (fun i : Fin s.length ↦ (d i : ℚ)) D I J)) :
    P ≤ RingHom.ker (WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot) ↔
      SourceCurveEmbeddingCoordinates.coordinateIdeal (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD P ≤
        RingHom.ker (SourceIntegerLift.evaluation D (SourceIntegerLift.point D x y w)).toRingHom := by
  have hmap := SourceIntegerLift.evaluation_comp d D I J hdeg hD x y w hroot
  constructor
  · intro h f hf
    change SourceIntegerLift.evaluation D (SourceIntegerLift.point D x y w) f = 0
    exact (RingHom.congr_fun hmap f).trans (RingHom.mem_ker.mp (h hf))
  · intro h z hz
    obtain ⟨f, hf⟩ := SourceProjectiveEmbedding.evaluation_surjective (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD z
    have hfP : f ∈ SourceCurveEmbeddingCoordinates.coordinateIdeal (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD P := by
      change SourceProjectiveEmbedding.evaluation (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD f ∈ P
      rw [hf]
      exact hz
    have hzero := RingHom.mem_ker.mp (h hfP)
    have heq := RingHom.congr_fun hmap f
    change WeightedRootEvaluation.sourceEvaluation d D I J x y w hroot z = 0
    rw [← hf]
    exact heq.symm.trans hzero

include hroot in
theorem embedded_degree_lower
    (p : letI := SourceVeroneseGrading.sourceGrading (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD
      ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece (fun i : Fin s.length ↦ (d i : ℚ)) D I J)) (hheight : ((SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p)).height = 1)
    (hpoint : SourceCurveEmbeddingCoordinates.coordinateIdeal (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p) ≤
      RingHom.ker (SourceIntegerLift.evaluation D (SourceIntegerLift.point D x y w)).toRingHom)
    (hcard : 2 ≤ s.length) (S T : Finset ℤ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisjI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hdisjJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (hneI : ∀ i, (I i).Nonempty) (hneJ : ∀ i, (J i).Nonempty)
    (hposS : ∀ z ∈ S, 0 < x + z) (hposT : ∀ z ∈ T, 0 < y + z)
    (hindS : EvenIndependentValues.Independent (SelectedProportionalPairs.values x S))
    (hindT : EvenIndependentValues.Independent (SelectedProportionalPairs.values y T))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values x S))
      (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values y T))) (hd : ∀ i, d i ≠ 0) :
    2 * (D : ℚ) ≤ GradedHilbertPolynomial.multiplicity
      (SourceCurveEmbeddingCoordinates.coordinatePiece (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p))
      (SourceProjectiveCurveEmbeddingHilbert.exists_polynomial s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight) := by
  rw [SourceProjectiveCurveEmbeddingHilbert.multiplicity_eq s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight]
  have hsource := (containment_iff s d D I J hdeg hD x y w hroot (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p)).mpr hpoint
  exact SourceProjectiveCurveLowDegreeExclusion.multiplicity_ge_twoD s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight x y
    (host_image s d D I J hs hD x y w hroot (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p) hsource) hcard S T hI hJ hdisjI hdisjJ hneI hneJ
    hposS hposT hindS hindT hdirect (fun i ↦ Int.cast_ne_zero.mpr (hd i))

end PaperP1.SourceIntegerCurvePoint
