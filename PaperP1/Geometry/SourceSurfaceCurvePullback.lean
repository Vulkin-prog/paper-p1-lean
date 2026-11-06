module

public import PaperP1.Geometry.SourceSurfaceComponentDegreeBudget
public import PaperP1.Geometry.FiniteHypersurfaceCurvePullback
public import PaperP1.Algebra.SourceSurfacePowerParameters

/-! # An actual projected curve of degree at most M lifts into at most Md literal source curves of degree at most Md -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceCurvePullback

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading
  SourceProjectiveCurveData LinearHypersurfaceImage

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
  (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
  (y : veronese c D I J) (hy : y ∈ sourcePiece c D I J 1)

include hc hne hI hJ hy

theorem uniform_curve_cover
    (Q : Ideal (CoordinateRing (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs) y))
    [Q.IsPrime]
    (hQ : letI := sourceGrading c D I J hdeg hD;
      letI := grading (sourcePiece c D I J) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs) y hy;
      Q.IsHomogeneous (piece (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs) y))
    (hheight : Q.height = 1) (E β : ℚ)
    (hcurve : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece
        (piece (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs) y) Q)
      (Polynomial.C E * Polynomial.X + Polynomial.C β))
    (M : ℕ) (hEM : E ≤ (M : ℚ)) :
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      curves.card ≤ M * (2 ^ s.length * D ^ 2) ∧
      (∀ Γ ∈ curves, degree s c D I J hs hdeg hD Γ ≤ ((M * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        Q ≤ RingHom.ker ((SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
          (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)).comp
            (toSource (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs) y)).toRingHom →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H := by
  let := sourceGrading c D I J hdeg hD
  let := source_isDomain s c D I J hs hc hne hI hJ
  let g := SourceSurfacePowerParameters.parameters s c D hD I J hs
  obtain ⟨e, h, _he, _h0, _hhom, hle, hf0, hf, hmem⟩ :=
    FiniteHypersurfaceCurvePullback.exists_equation (sourcePiece c D I J) g
      (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs) y hy
      (SourceSurfacePowerParameters.finite s c D hD I J hs hdeg)
      (SourceSurfacePowerParameters.injective s c D hD I J hs) Q hQ hheight E β hcurve
  obtain ⟨curves, hcount, hdegrees, hcover⟩ :=
    SourceSurfaceComponentDegreeBudget.uniform_section_curve_cover s c D I J hs hdeg hD hc hne hI hJ
      e (aeval (R := ℚ) g h) hf hf0
  have heM : e ≤ M := by exact_mod_cast hle.trans hEM
  have hbound := Nat.mul_le_mul_right (2 ^ s.length * D ^ 2) heM
  refine ⟨curves, hcount.trans hbound, ?_, ?_⟩
  · intro Γ hΓ
    exact (hdegrees Γ hΓ).2.trans (by exact_mod_cast hbound)
  · intro H v hv hpoint
    apply hcover H v hv
    have hz := hpoint hmem
    change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
      (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)
      (toSource (F := ℚ) g y (parameterMap (F := ℚ) g y h)) = 0 at hz
    have heval := DFunLike.congr_fun (parameterMap_toSource (F := ℚ) g y) h
    change toSource (F := ℚ) g y (parameterMap (F := ℚ) g y h) = aeval (R := ℚ) g h at heval
    rwa [heval] at hz

end PaperP1.SourceSurfaceCurvePullback
