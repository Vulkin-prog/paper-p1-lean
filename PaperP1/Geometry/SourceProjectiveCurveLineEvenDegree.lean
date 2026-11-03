module

public import PaperP1.Geometry.SourceProjectiveCurveGraphExclusion
public import PaperP1.Geometry.SourceProjectiveCurveVerticalExclusion
public import PaperP1.Algebra.HomogeneousAffineLineClassification
public import PaperP1.Geometry.ProjRankOneQuadraticDescent
public import PaperP1.Algebra.SourceCurveRadicalRelations
public import PaperP1.Algebra.NativeVeroneseLineChart
public import PaperP1.Arithmetic.SplitRadicalLineObstruction
public import PaperP1.Geometry.SourceProjectiveCurveSmallDegree

/-! # Actual source curves over lines through admissible affine hosts have even function-field degree -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveLineEvenDegree

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


theorem degree_even
    (f : MvPolynomial (Fin 3) ℚ) (hf0 : f ≠ 0) (hf : f.IsHomogeneous 1)
    (hbase : SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) =
      PlaneCurveVeroneseBaseQuotient.ideal ℚ f D)
    (x y : ℤ)
    (hhost : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) ≤
      RingHom.ker (AffineLineClassification.valueMap (x : ℚ) (y : ℚ)))
    (hcard : 2 ≤ s.length) (S T : Finset ℤ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisjI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hdisjJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (hneI : ∀ i, (I i).Nonempty) (hneJ : ∀ i, (J i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hindS : EvenIndependentValues.Independent (SelectedProportionalPairs.values x S))
    (hindT : EvenIndependentValues.Independent (SelectedProportionalPairs.values y T))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values x S))
      (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values y T))) (hc : ∀ i, c i ≠ 0) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦ Even m)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p) := by
  apply Nat.not_odd_iff_even.mp
  intro hdegree
  have himage := (congrArg (NativeVeroneseAffineIdeal.affineIdeal ℚ D) hbase).trans
    (NativeVeroneseAffineIdeal.contracted_principal f hf D hD)
  have hfmem : NativeAffineChart.specialization ℚ f ∈ NativeVeroneseAffineIdeal.affineIdeal ℚ D
      (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
    himage.symm ▸ Ideal.mem_span_singleton_self _
  have hpoint := RingHom.mem_ker.mp (hhost hfmem)
  rcases HomogeneousAffineLineClassification.classify f hf hf0 (x : ℚ) (y : ℚ) hpoint with
    ⟨α, β, hgraph, hline⟩ | hvertical
  · exact SourceProjectiveCurveGraphExclusion.no_odd_degree s c D I J hs hdeg hD p hdegree
      α β (himage.trans hgraph) hcard S T x y hI hJ hdisjI hneI hposS hposT hindS hdirect hline hc
  · exact SourceProjectiveCurveVerticalExclusion.no_odd_degree s c D I J hs hdeg hD p hdegree
      x y (himage.trans hvertical) hcard S T hI hJ hdisjJ hneJ hposS hposT hindT hdirect hc


end PaperP1.SourceProjectiveCurveLineEvenDegree
