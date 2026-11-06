module

public import PaperP1.Geometry.SourceCurveOrdinaryImagePrime
public import PaperP1.Geometry.SourceProjectiveCurveIdealData
public import PaperP1.Geometry.OrdinarySurfaceCurveData
public import PaperP1.Algebra.LinearCoordinateCurveImageDegree
public import PaperP1.Algebra.LinearHilbertSlopeComparison

/-! # An actual source curve meeting the normalized chart constructs its actual ordinary image curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceProjectiveCurveToOrdinary

open Polynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance weightedRing (ι : Type*) : CommRing (HomogeneousSplitRadicalRelations.WeightedPolynomial ℚ ι) := inferInstance
local instance sourceRing (ι : Type*) (c : ι → ℚ) (D : ℕ) (I J : ι → Finset ℤ) :
    CommRing (veronese c D I J) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)

include hmin in
theorem exists_curve (Γ : SourceProjectiveCurveData.Curve s c D I J hdeg hD)
    (hz : OrdinaryCurveSourcePoint.sourceZ c D I J ∉ SourceProjectiveCurveData.sourceIdeal s c D I J hdeg hD Γ) :
    ∃ Δ : OrdinarySurfaceCurveData.Curve c D I J,
      Δ.ideal = SourceCurveOrdinaryImagePrime.ideal c D hD I J
        (SourceProjectiveCurveData.sourceIdeal s c D I J hdeg hD Γ) ∧
      (Δ.degree : ℚ) ≤ SourceProjectiveCurveData.degree s c D I J hs hdeg hD Γ ∧
      SourceProjectiveCurveData.degree s c D I J hs hdeg hD Γ ≤ (Δ.degree : ℚ) * (D : ℚ) := by
  let := sourceGrading c D I J hdeg hD
  let P := SourceProjectiveCurveData.sourceIdeal s c D I J hdeg hD Γ
  let : P.IsPrime := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD Γ.point
  have hP : P.IsHomogeneous (sourcePiece c D I J) :=
    SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD Γ.point
  let H := HomogeneousQuotientGrading.piece (sourcePiece c D I J) P
  let (n : ℕ) : Module.Finite ℚ (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  let (n : ℕ) : Module.Finite ℚ (H n) :=
    HomogeneousQuotientGrading.piece_finite (sourcePiece c D I J) P n
  let E := SourceProjectiveCurveData.degree s c D I J hs hdeg hD Γ
  let b := (SourceProjectiveCurveData.toCurve s c D I J hs hdeg hD Γ).constant
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial H (C E * X + C b) :=
    SourceProjectiveCurveIdealData.hilbert s c D I J hs hdeg hD Γ
  let g (i : Fin 3 ⊕ Fin s.length) := Ideal.Quotient.mk P (OrdinarySourcePolynomialProjection.coordinate c D hD I J i)
  have hg (i : Fin 3 ⊕ Fin s.length) : g i ∈ H 1 :=
    Submodule.mem_map.mpr ⟨_, OrdinarySourcePolynomialProjection.coordinate_mem c D hD I J i, rfl⟩
  let : IsDomain (veronese c D I J ⧸ P) := inferInstance
  let : GradedAlgebra H := HomogeneousQuotientGrading.grading (sourcePiece c D I J) P hP
  obtain ⟨d, β, hd, hle⟩ := LinearCoordinateCurveImageDegree.exists_nat_linear_hilbert
    (F := ℚ) (R := veronese c D I J ⧸ P) (σ := Fin 3 ⊕ Fin s.length) H E b hp g hg
  let Q := SourceCurveOrdinaryImagePrime.ideal c D hD I J P
  let : Q.IsPrime := SourceCurveOrdinaryImagePrime.prime c D hD I J P
  have hrel := SourceCurveOrdinaryImagePrime.relations c D hD I J P hmin hdeg
  have hQ := SourceCurveOrdinaryImagePrime.homogeneous c D hD I J P hdeg hP
  have hchart := SourceCurveOrdinaryImagePrime.chart_not_mem c D hD I J P hz
  have hPeq := SourceCurveOrdinaryImagePrime.sourceIdeal_eq c D hD I J P hmin hdeg hP hz
  have hd' : GradedHilbertPolynomial.IsHilbertPolynomial (OrdinaryCurveSourceMap.ordinaryPiece Q)
      (C (d : ℚ) * X + C β) := hd
  have hp' : GradedHilbertPolynomial.IsHilbertPolynomial
      (OrdinaryCurveSourceMap.sourcePiece c D I J hD hmin hdeg Q hrel hQ) (C E * X + C b) := by
    change GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (sourcePiece c D I J)
        (OrdinaryCurveSourceMap.sourceIdeal c D I J hD hmin hdeg Q hrel hQ)) _
    rw [hPeq]
    exact hp
  let (n : ℕ) : Module.Finite ℚ (OrdinaryCurveSourceMap.ordinaryPiece Q n) :=
    OrdinaryCurveSourceMap.ordinaryPiece_finite Q n
  have hreverse : E ≤ (d : ℚ) * (D : ℚ) := LinearHilbertSlopeComparison.slope_le_of_injective
    (OrdinaryCurveSourceMap.sourcePiece c D I J hD hmin hdeg Q hrel hQ)
    (OrdinaryCurveSourceMap.ordinaryPiece Q) E (d : ℚ)
    (LinearHilbertGrowth.of_affine_polynomial hp') (LinearHilbertGrowth.of_affine_polynomial hd') D hD
    (OrdinaryCurveSourceMap.curveMap c D I J hD hmin hdeg Q hrel hQ).toLinearMap
    (OrdinaryCurveSourceMap.curveMap_injective c D I J hD hmin hdeg Q hrel hQ)
    (OrdinaryCurveSourceMap.curveMap_mem c D I J hD hmin hdeg Q hrel hQ)
  have hdpos : 0 < d := by
    by_contra hn
    have he : d = 0 := Nat.eq_zero_of_not_pos hn
    have hE : 0 < E := SourceProjectiveCurveData.degree_pos s c D I J hs hdeg hD Γ
    simp only [he, Nat.cast_zero, zero_mul] at hreverse
    exact (not_lt_of_ge hreverse) hE
  have hheight : (OrdinaryCurveSourceHeight.surfaceIdeal c D I J Q hrel).height = 1 := by
    rw [← OrdinaryCurveSourceHeight.height_eq c D I J Q hrel hD hmin hdeg hQ hchart, hPeq]
    exact Γ.height
  let Δ : OrdinarySurfaceCurveData.Curve c D I J := {
    ideal := Q
    prime := inferInstance
    homogeneous := hQ
    relations := hrel
    height := hheight
    degree := d
    degree_pos := hdpos
    constant := β
    hilbert := hd' }
  exact ⟨Δ, rfl, hle, hreverse⟩

end PaperP1.SourceProjectiveCurveToOrdinary
