module

public import PaperP1.Arithmetic.UniformNormalizedCurvePointCount
public import PaperP1.Arithmetic.SourceIntegerPoints
public import PaperP1.Geometry.SourceProjectiveCurveData

/-! # The source-embedding curve-count specialization follows from the single generic curve input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformSourceCurvePointCount

open PaperP1.HomogeneousSplitRadicalData PaperP1.SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance generatorFinite (k D : ℕ) : Finite (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin k) D) :=
  SourceProjectiveEmbedding.index_finite ℚ (Fin k) D

theorem source_points (k D H : ℕ)
    (Q : Ideal (MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin k) D) ℚ)) :
    NormalizedIntegerPoints.points Q (SourceIntegerPoints.normalizer D) H =
      SourceIntegerPoints.curvePoints D Q H := by
  classical
  ext v
  rw [NormalizedIntegerPoints.mem_points, SourceIntegerPoints.mem_curvePoints]
  rfl

theorem uniform_bound (kmax D M : ℕ)
    (hPila : UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + kmax) M)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : List (PolynomialRing ℚ), s.length ≤ kmax →
      ∀ (c : Fin s.length → ℚ) (I J : Fin s.length → Finset ℤ),
      ∀ (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D),
      ∀ Γ : Curve s c D I J hdeg hD, degree s c D I J hs hdeg hD Γ ≤ (M : ℚ) →
      ∀ H : ℕ, 1 ≤ H →
      ((SourceIntegerPoints.curvePoints D (ideal s c D I J hdeg hD Γ) H).card : ℝ) ≤
        A * (H : ℝ) ^ (1 / (degree s c D I J hs hdeg hD Γ : ℝ) + δ) := by
  obtain ⟨A, hA, hcount⟩ := hPila δ hδ
  refine ⟨A, hA, ?_⟩
  intro s hlength c I J hs hdeg hD Γ hM H hH
  have hdim : Nat.card (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D) ≤
      (D + 2).choose 2 + kmax := by
    rw [SourceProjectiveEmbedding.coordinate_count_fin]
    omega
  have hbound := hcount (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D) hdim
    (toCurve s c D I J hs hdeg hD Γ) hM (SourceIntegerPoints.normalizer D) H hH
  simpa only [toCurve_ideal, toCurve_degree, source_points] using hbound

end PaperP1.UniformSourceCurvePointCount
