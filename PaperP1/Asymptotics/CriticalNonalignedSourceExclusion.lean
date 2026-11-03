module

public import PaperP1.Asymptotics.CriticalNonalignedRationalExclusion
public import PaperP1.Geometry.SourceProjectiveCurveBoundedDegree
public import PaperP1.Geometry.SourceCurveHostChart
public import PaperP1.Geometry.SourceCurveAffineRadicalCover

/-! # Actual projective source-curve exclusion from nonalignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalNonalignedSourceExclusion

open Polynomial Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SelectedProportionalPairs

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance nativeRing : CommRing (MvPolynomial (Fin 3) ℚ) := inferInstance
local instance affineRing : CommRing ℚ[X][X] := inferInstance

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (s : List (PolynomialRing ℚ)) (d : Fin s.length → ℤ) (D : ℕ)
        (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i))
        (hdeg : ∀ i, (I i).card + (J₀ i).card ≤ 2 * D) (hD : 0 < D),
      ∀ (p : letI := SourceVeroneseGrading.sourceGrading c D I J₀ hdeg hD
        ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J₀)),
      ∀ (hheight : (SourceCurveProjectivePointData.ideal s c D I J₀ hdeg hD p).height = 1),
        GradedHilbertPolynomial.multiplicity
          (SourceCurveQuotient.sourcePiece s c D I J₀ (SourceCurveProjectivePointData.ideal s c D I J₀ hdeg hD p))
          (SourceProjectiveCurveDegree.exists_polynomial s c D I J₀ hs hdeg hD p hheight) ≤ (D : ℚ) * (E : ℚ) →
        4 * (E + 1) ^ 2 ≤ s.length →
      ∀ (a : ℕ), 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i k ↦ Disjoint (I i) (I k)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → (N : ℤ) ≤ Y → Y.natAbs ≤ 2 * N →
        NativeVeroneseAffineIdeal.affineIdeal ℚ D
          (SourceCurveQuotient.baseIdeal s c D I J₀ hs hD (SourceCurveProjectivePointData.ideal s c D I J₀ hdeg hD p)) ≤
          RingHom.ker (AffineLineClassification.valueMap (X : ℚ) (Y : ℚ)) →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        ¬ AffineGridAlignment.Aligned B X Y →
        False := by
  obtain ⟨N₀, hN₀⟩ := CriticalNonalignedRationalExclusion.eventually_no_dyadic_point.{0,0} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL s d D I j c J₀ hs hdeg hD p hheight hbound hlarge a ha hd hI hj hcard hiB hjB S T hiS hjT X Y hXN hYNlower hYN hhost hposS hposT hnonaligned
  let P := SourceCurveProjectivePointData.ideal s c D I J₀ hdeg hD p
  let := SourceCurveProjectivePointData.ideal_prime s c D I J₀ hdeg hD p
  have hP := SourceCurveProjectivePointData.ideal_homogeneous s c D I J₀ hdeg hD p
  obtain ⟨e, f, he, hf0, hf, hirr, hbase, heE, hrE⟩ :=
    SourceProjectiveCurveBoundedDegree.exists_bounded_equation s c D I J₀ hs hdeg hD p hheight E hbound
  let : Fact (Irreducible f) := ⟨hirr⟩
  have hZf := SourceCurveHostChart.not_infinity D (SourceCurveQuotient.baseIdeal s c D I J₀ hs hD P)
    (X : ℚ) (Y : ℚ) hhost f hD hbase
  let g := NativeAffineChart.specialization ℚ f
  let : Fact (Irreducible g) := ⟨HomogeneousAffinePrincipalChart.affine_irreducible f hf hZf⟩
  have himage : NativeVeroneseAffineIdeal.affineIdeal ℚ D (SourceCurveQuotient.baseIdeal s c D I J₀ hs hD P) =
      AffineCurveFunctionField.ideal g :=
    (congrArg (NativeVeroneseAffineIdeal.affineIdeal ℚ D) hbase).trans
      (NativeVeroneseAffineIdeal.contracted_principal f hf D hD)
  have hZ := SourceCurveHostChart.coordinate_ne_zero D (SourceCurveQuotient.baseIdeal s c D I J₀ hs hD P)
    (X : ℚ) (Y : ℚ) hhost
  obtain ⟨K, instK, algK, hfinite, hdegree, r, hr⟩ :=
    SourceCurveAffineRadicalCover.exists_cover s c D I J₀ hs hD P hdeg hP g himage hZ
  let := instK
  let := algK
  let := hfinite
  have hKE : Module.finrank (AffineCurveFunctionField.FunctionField g) K ≤ E := hdegree.trans_le hrE
  have hdegrees := HomogeneousAffineDegree.partial_degrees_le f hf
  have hpoint := SourceCurveHostChart.affine_point D (SourceCurveQuotient.baseIdeal s c D I J₀ hs hD P)
    (X : ℚ) (Y : ℚ) hhost f hf hD hbase
  exact hN₀ N hN L B hcrit hB hBL g (hdegrees.1.trans heE) (hdegrees.2.trans heE) K hKE (Fin s.length)
    (by simpa only [Fintype.card_fin] using hlarge) a ha d hd I j hI hj hcard hiB hjB r hr
    S T hiS hjT X Y hXN hYNlower hYN hpoint hposS hposT hnonaligned

end PaperP1.CriticalNonalignedSourceExclusion
