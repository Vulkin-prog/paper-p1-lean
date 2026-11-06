module

public import PaperP1.Algebra.SourceSurfaceSectionHilbert
public import PaperP1.Algebra.GradedQuotientHilbertMonotonicity
public import PaperP1.Geometry.SourcePrincipalComponentCurves

/-! # Every actual source-projective curve on a nonzero surface divisor has degree at most the genuine divisor degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceSectionCurveDegree

open Polynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading
  SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
  (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
  (e : ℕ) (f : veronese c D I J) (hf : f ∈ sourcePiece c D I J e) (hf0 : f ≠ 0)

include hc hne hI hJ hf hf0

theorem degree_le (Γ : Curve s c D I J hdeg hD) (hΓ : f ∈ sourceIdeal s c D I J hdeg hD Γ) :
    degree s c D I J hs hdeg hD Γ ≤ ((e * (2 ^ s.length * D ^ 2) : ℕ) : ℚ) := by
  let := sourceGrading c D I J hdeg hD
  let (n : ℕ) : Module.Finite ℚ (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  let P := sourceIdeal s c D I J hdeg hD Γ
  have hP := SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD Γ.point
  obtain ⟨b, hb⟩ := SourceSurfaceSectionHilbert.exists_linear_hilbert s c D hD I J hs hdeg hc hne hI hJ e f hf hf0
  let β := (toCurve s c D I J hs hdeg hD Γ).constant
  have hcoord : GradedHilbertPolynomial.IsHilbertPolynomial
      (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD P)
      (C (degree s c D I J hs hdeg hD Γ) * X + C β) :=
    (toCurve s c D I J hs hdeg hD Γ).hilbert
  have hcurve : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (sourcePiece c D I J) P)
      (C (degree s c D I J hs hdeg hD Γ) * X + C β) :=
    (GradedHilbertTransport.isHilbertPolynomial_iff _ _
      (fun n ↦ SourceCurveEmbeddingCoordinates.piece_finrank c D I J hdeg hD P hP n) _).mp hcoord
  have hle : HomogeneousPrincipalQuotient.ideal f ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hΓ
  have hh := GradedQuotientHilbertMonotonicity.coefficient_le (sourcePiece c D I J)
    (HomogeneousPrincipalQuotient.ideal f) P hle _ _ 1 (by compute_degree) (by compute_degree) hb hcurve
  simpa only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_succ, mul_one, add_zero] using hh

theorem bounded_degree_finite_cover :
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      (∀ Γ ∈ curves, f ∈ sourceIdeal s c D I J hdeg hD Γ ∧
        degree s c D I J hs hdeg hD Γ ≤ ((e * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
          (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv) f = 0 →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (ideal s c D I J hdeg hD Γ) H := by
  obtain ⟨curves, hcurves, hcover⟩ := SourcePrincipalComponentCurves.finite_curve_cover s c D I J hdeg hD
    hs hc hne hI hJ e f hf hf0
  refine ⟨curves, ?_, hcover⟩
  intro Γ hΓ
  exact ⟨hcurves Γ hΓ, degree_le s c D I J hs hdeg hD hc hne hI hJ e f hf hf0 Γ (hcurves Γ hΓ)⟩

end PaperP1.SourceSurfaceSectionCurveDegree
