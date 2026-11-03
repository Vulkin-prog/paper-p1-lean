module

public import PaperP1.Geometry.SourceProjectiveCurveLineSquares
public import PaperP1.Geometry.ProjRankOneQuadraticDescent
public import PaperP1.Algebra.SourceCurveRadicalRelations
public import PaperP1.Algebra.NativeVeroneseLineChart
public import PaperP1.Arithmetic.SplitRadicalLineObstruction
public import PaperP1.Geometry.SourceProjectiveCurveSmallDegree

/-! # Actual source curves over graph lines through admissible hosts have multiplicity at least 2D -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveGraphExclusion

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


theorem no_odd_degree
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ Odd m)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
    (α β : ℚ)
    (himage : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) =
      Ideal.span {NativeVeroneseLineChart.equation α β})
    (hcard : 2 ≤ s.length) (S T : Finset ℤ) (x y : ℤ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisj : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hne : ∀ i, (I i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (SelectedProportionalPairs.values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values x S))
      (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values y T)))
    (hhost : (y : ℚ) = α * (x : ℚ) + β) (hc : ∀ i, c i ≠ 0) : False := by
  apply SplitRadicalLineObstruction.family_obstruction (Finset.univ : Finset (Fin s.length))
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hcard) S T I J x y α β c
    (fun i _ ↦ hI i) (fun i _ ↦ hJ i) (fun _ _ _ _ hij ↦ hdisj hij)
    (fun i _ ↦ hne i) hposS hposT hind hdirect hhost (fun i _ ↦ hc i)
  intro i _
  exact SourceProjectiveCurveLineSquares.lineRestriction_isSquare_of_odd_degree s c D I J hs hdeg hD p hdegree α β himage i

theorem no_degree_one
    (hdegree : beta% (fun {m n : ℕ} (_ : m = n) ↦ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
    (α β : ℚ)
    (himage : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) =
      Ideal.span {NativeVeroneseLineChart.equation α β})
    (hcard : 2 ≤ s.length) (S T : Finset ℤ) (x y : ℤ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisj : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hne : ∀ i, (I i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (SelectedProportionalPairs.values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values x S))
      (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values y T)))
    (hhost : (y : ℚ) = α * (x : ℚ) + β) (hc : ∀ i, c i ≠ 0) : False := by
  exact no_odd_degree s c D I J hs hdeg hD p
    (hdegree.symm ▸ (by decide : Odd (1 : ℕ))) α β himage hcard S T x y hI hJ hdisj hne hposS hposT hind hdirect hhost hc

theorem multiplicity_ge_twoD
    (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1)
    (α β : ℚ)
    (himage : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) =
      Ideal.span {NativeVeroneseLineChart.equation α β})
    (hcard : 2 ≤ s.length) (S T : Finset ℤ) (x y : ℤ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisj : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hne : ∀ i, (I i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (SelectedProportionalPairs.values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values x S))
      (FiniteEvenSquareClasses.space (SelectedProportionalPairs.values y T)))
    (hhost : (y : ℚ) = α * (x : ℚ) + β) (hc : ∀ i, c i ≠ 0) : 2 * (D : ℚ) ≤ GradedHilbertPolynomial.multiplicity
      (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight) := by
  by_contra hnot
  obtain ⟨f, hf0, hf, hirr, hbase, hdegree⟩ :=
    SourceProjectiveCurveSmallDegree.line_and_degree_one s c D I J hs hdeg hD p hheight (lt_of_not_ge hnot)
  exact no_degree_one s c D I J hs hdeg hD p hdegree α β himage hcard S T x y
    hI hJ hdisj hne hposS hposT hind hdirect hhost hc

end PaperP1.SourceProjectiveCurveGraphExclusion
