module

public import PaperP1.Arithmetic.SourceIntegerPointHeight
public import PaperP1.Geometry.OrdinaryCurveHostImage
public import PaperP1.Geometry.SourceProjectiveCurveNonalignedDegreeBound
public import PaperP1.Geometry.SourceIntegerCurvePoint
public import PaperP1.Geometry.SourceProjectiveCurveEmbeddingHilbert

/-! # Actual embedded integer-root point containment supplies the source host and embedded curve degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerNonalignedCurvePoint

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

include hroot in
theorem embedded_degree_lower
    (p : letI := SourceVeroneseGrading.sourceGrading (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD
      ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece (fun i : Fin s.length ↦ (d i : ℚ)) D I J)) (hheight : ((SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p)).height = 1)
    (hpoint : SourceCurveEmbeddingCoordinates.coordinateIdeal (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p) ≤
      RingHom.ker (SourceIntegerLift.evaluation D (SourceIntegerLift.point D x y w)).toRingHom)
    (hcard : 2 ≤ s.length) (B : ℕ)
    (hdisjI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hneI : ∀ i, (I i).Nonempty) (hneJ : ∀ i, (J i).Nonempty)
    (hI : ∀ ν i, i ∈ I ν → i.natAbs ≤ B)
    (hJ : ∀ ν j, j ∈ J ν → j.natAbs ≤ B)
    (hX : (B : ℤ) < x) (hY : (B : ℤ) < y)
    (hnon : ¬ AffineGridAlignment.Aligned B x y) (hd : ∀ i, d i ≠ 0) :
    2 * (D : ℚ) ≤ GradedHilbertPolynomial.multiplicity
      (SourceCurveEmbeddingCoordinates.coordinatePiece (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p))
      (SourceProjectiveCurveEmbeddingHilbert.exists_polynomial s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight) := by
  rw [SourceProjectiveCurveEmbeddingHilbert.multiplicity_eq s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight]
  have hsource := (SourceIntegerCurvePoint.containment_iff s d D I J hdeg hD x y w hroot (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p)).mpr hpoint
  exact SourceProjectiveCurveNonalignedDegreeBound.multiplicity_ge_twoD s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hs hdeg hD p hheight x y
    (SourceIntegerCurvePoint.host_image s d D I J hs hD x y w hroot (SourceCurveProjectivePointData.ideal s (fun i : Fin s.length ↦ (d i : ℚ)) D I J hdeg hD p) hsource) hcard B hdisjI hneI hneJ hI hJ hX hY hnon
    (fun i ↦ Int.cast_ne_zero.mpr (hd i))

end PaperP1.SourceIntegerNonalignedCurvePoint
