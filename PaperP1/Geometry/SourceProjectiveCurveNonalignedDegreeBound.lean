module

public import PaperP1.Geometry.SourceProjectiveCurveLineSquares
public import PaperP1.Geometry.SourceProjectiveCurveVerticalSquares
public import PaperP1.Algebra.HomogeneousAffineLineClassification
public import PaperP1.Geometry.ProjRankOneQuadraticDescent
public import PaperP1.Algebra.SourceCurveRadicalRelations
public import PaperP1.Algebra.NativeVeroneseLineChart
public import PaperP1.Arithmetic.SquareLineFamilyAlignment
public import PaperP1.Geometry.SourceProjectiveCurveSmallDegree

/-! # Actual height-one source curves through nonaligned affine hosts have multiplicity at least 2D -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveNonalignedDegreeBound

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)


theorem multiplicity_ge_twoD
    (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1)
    (x y : ℤ)
    (hhost : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) ≤
      RingHom.ker (AffineLineClassification.valueMap (x : ℚ) (y : ℚ)))
    (hcard : 2 ≤ s.length) (B : ℕ)
    (hdisjI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hneI : ∀ i, (I i).Nonempty) (hneJ : ∀ i, (J i).Nonempty)
    (hI : ∀ ν i, i ∈ I ν → i.natAbs ≤ B)
    (hJ : ∀ ν j, j ∈ J ν → j.natAbs ≤ B)
    (hX : (B : ℤ) < x) (hY : (B : ℤ) < y)
    (hnon : ¬ AffineGridAlignment.Aligned B x y) (hc : ∀ i, c i ≠ 0) :
    2 * (D : ℚ) ≤ GradedHilbertPolynomial.multiplicity
      (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight) := by
  by_contra hnot
  obtain ⟨f, hf0, hf, hirr, hbase, hdegree⟩ :=
    SourceProjectiveCurveSmallDegree.line_and_degree_one s c D I J hs hdeg hD p hheight (lt_of_not_ge hnot)
  have himage := (congrArg (NativeVeroneseAffineIdeal.affineIdeal ℚ D) hbase).trans
    (NativeVeroneseAffineIdeal.contracted_principal f hf D hD)
  have hfmem : NativeAffineChart.specialization ℚ f ∈ NativeVeroneseAffineIdeal.affineIdeal ℚ D
      (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
    himage.symm ▸ Ideal.mem_span_singleton_self _
  have hpoint := RingHom.mem_ker.mp (hhost hfmem)
  rcases HomogeneousAffineLineClassification.classify f hf hf0 (x : ℚ) (y : ℚ) hpoint with
    ⟨α, β, hgraph, hline⟩ | hvertical
  · have hsq := SourceProjectiveCurveLineSquares.lineRestriction_isSquare
      s c D I J hs hdeg hD p hdegree α β (himage.trans hgraph)
    exact hnon (SquareLineFamilyAlignment.of_family hcard B x y α β c hc I J hdisjI hneI
      hI hJ hsq hX hY hline)
  · let ν : Fin s.length := ⟨0, by omega⟩
    have hsq := SourceProjectiveCurveVerticalSquares.verticalRestriction_isSquare
      s c D I J hs hdeg hD p hdegree (x : ℚ) (himage.trans hvertical) ν
    exact SquareLineFamilyAlignment.vertical_not_square B x (c ν) (hc ν)
      (I ν) (J ν) (hneJ ν) (hI ν) hX hsq

end PaperP1.SourceProjectiveCurveNonalignedDegreeBound
