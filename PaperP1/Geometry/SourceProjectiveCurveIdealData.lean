module

public import PaperP1.Geometry.SourceProjectiveCurveData
public import PaperP1.Geometry.ProjectiveCurveHilbertDegree

/-! # The literal source curve is determined by its prime and has its actual source-quotient Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceProjectiveCurveIdealData

open Polynomial HomogeneousSplitRadicalData SourceVeroneseGrading SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)

theorem sourceIdeal_injective : Function.Injective (sourceIdeal s c D I J hdeg hD) := by
  let := sourceGrading c D I J hdeg hD
  intro Γ Δ he
  have hp : Γ.point = Δ.point := ProjectiveSpectrum.ext (HomogeneousIdeal.ext he)
  cases Γ
  cases Δ
  cases hp
  rfl

theorem hilbert (Γ : Curve s c D I J hdeg hD) :
    GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (sourcePiece c D I J) (sourceIdeal s c D I J hdeg hD Γ))
      (C (degree s c D I J hs hdeg hD Γ) * X + C (toCurve s c D I J hs hdeg hD Γ).constant) := by
  let := sourceGrading c D I J hdeg hD
  exact (GradedHilbertTransport.isHilbertPolynomial_iff _ _
    (fun n ↦ SourceCurveEmbeddingCoordinates.piece_finrank c D I J hdeg hD
      (sourceIdeal s c D I J hdeg hD Γ)
      (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD Γ.point) n) _).mp
    (toCurve s c D I J hs hdeg hD Γ).hilbert

theorem one_le_degree (Γ : Curve s c D I J hdeg hD) :
    1 ≤ degree s c D I J hs hdeg hD Γ := by
  let G := toCurve s c D I J hs hdeg hD Γ
  have hpos := ProjectiveCurveHilbertDegree.natDegree_pos G
  have hcast := ProjectiveCurveHilbertDegree.natDegree_cast G
  change 1 ≤ G.degree
  rw [← hcast]
  exact_mod_cast hpos

end PaperP1.SourceProjectiveCurveIdealData
