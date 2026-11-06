module

public import PaperP1.Algebra.NormalizedGradedPoint
public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Arithmetic.SourceIntegerPointEvaluation
public import PaperP1.Algebra.BivariateQuadraticTowerPoints
public import Mathlib.Algebra.Algebra.Hom.Rat
public import PaperP1.Algebra.QuadraticTowerRootBasis
public import PaperP1.Arithmetic.SplitRadicalPointHeight

/-! # Every actual normalized integer source point has the literal integer affine radical equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceNativeIntegerPoint
open PaperP1 Polynomial MvPolynomial HomogeneousSplitRadicalData
  HomogeneousSplitRadicalRelations HomogeneousSplitRadicalGrading HomogeneousSplitRadicalFiniteVeronese
  HomogeneousSplitRadicalVeronese SourceVeroneseGrading SourceProjectiveEmbedding
  VeroneseCoordinateCharts

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

theorem generator_normalizer : sourceGenerator c D I J (SourceIntegerPoints.normalizer D) =
    sourceCoordinate c D I J hdeg 2 := by
  apply Subtype.ext
  change quotientMap c D I J (rename Sum.inl (monomial (Finsupp.single (2 : Fin 3) D) 1)) = _
  rw [← MvPolynomial.X_pow_eq_monomial, map_pow, rename_X]
  rfl

def evaluation (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) :
    SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J →+* ℚ := by
  let := sourceGrading c D I J hdeg hD
  have hh : SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (sourceCoordinate c D I J hdeg 2) = 1 := by
    rw [← generator_normalizer s c D I J hdeg, SourceIntegerPointEvaluation.evaluation_coordinate,
      hn, Int.cast_one]
  exact (NormalizedGradedPoint.evaluation (sourcePiece c D I J)
    (sourceCoordinate_mem c D I J hdeg 2)
    (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv).toRingHom hh).comp
      (SourceAffineChart.affineEquiv s c D I J hdeg hs hD).symm.toRingHom

theorem evaluation_specialization (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (x : veronese c D I J) :
    evaluation s c D I J hdeg hD hs v hv hn
      (SourceAffineChartCoordinates.specialization s c D I J hs (x : CoordinateRing c D I J)) =
      SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv x := by
  let := sourceGrading c D I J hdeg hD
  rw [← SourceAffineChartCoordinates.equiv_dehomogenization s c D I J hdeg hs hD x]
  have hh : SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (sourceCoordinate c D I J hdeg 2) = 1 := by
    rw [← generator_normalizer s c D I J hdeg, SourceIntegerPointEvaluation.evaluation_coordinate,
      hn, Int.cast_one]
  change (NormalizedGradedPoint.evaluation (sourcePiece c D I J)
    (sourceCoordinate_mem c D I J hdeg 2)
    (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv).toRingHom hh)
      ((SourceAffineChart.affineEquiv s c D I J hdeg hs hD).symm
        (SourceAffineChart.affineEquiv s c D I J hdeg hs hD
          (GradedDehomogenization.map (sourcePiece c D I J)
            (sourceCoordinate_mem c D I J hdeg 2) x))) = _
  rw [RingEquiv.symm_apply_apply]
  exact NormalizedGradedPoint.evaluation_dehomogenization (sourcePiece c D I J)
    (sourceCoordinate_mem c D I J hdeg 2)
    (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv).toRingHom hh x

theorem native_specialization_variables :
    NativeAffineChart.specialization ℚ (MvPolynomial.X (0 : Fin 3)) = (Polynomial.X : ℚ[X][X]) ∧
    NativeAffineChart.specialization ℚ (MvPolynomial.X (1 : Fin 3)) = Polynomial.C (Polynomial.X : ℚ[X]) ∧
    NativeAffineChart.specialization ℚ (MvPolynomial.X (2 : Fin 3)) = 1 := by
  simp [NativeAffineChart.specialization, HomogeneousSplitRadicalChart.chart,
    TrivariatePolynomialEquiv.threeEquiv_X_zero, TrivariatePolynomialEquiv.threeEquiv_X_one,
    TrivariatePolynomialEquiv.threeEquiv_X_two]

theorem specialization_affine_generator (j : Fin 3) :
    SourceAffineChartCoordinates.specialization s c D I J hs
      (sourceGenerator c D I J (SourceIntegerPoints.affineIndex D hD j) : CoordinateRing c D I J) =
      algebraMap ℚ[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J)
        (NativeAffineChart.specialization ℚ (MvPolynomial.X j)) := by
  change SourceAffineChartCoordinates.specialization s c D I J hs
    (HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J
      (monomial (Finsupp.single j 1 + Finsupp.single (2 : Fin 3) (D - 1)) 1)) = _
  rw [SourceAffineChartCoordinates.specialization_base, MvPolynomial.monomial_add_single,
    ← MvPolynomial.X_pow_eq_monomial, pow_one, map_mul, map_pow, native_specialization_variables.2.2,
    one_pow, mul_one]


theorem evaluation_affine (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (j : Fin 3) :
    evaluation s c D I J hdeg hD hs v hv hn
      (algebraMap ℚ[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J)
        (NativeAffineChart.specialization ℚ (MvPolynomial.X j))) =
      (v (SourceIntegerPoints.affineIndex D hD j) : ℚ) := by
  rw [← specialization_affine_generator s c D I J hD hs,
    evaluation_specialization s c D I J hdeg hD hs,
    SourceIntegerPointEvaluation.evaluation_coordinate]

theorem evaluation_radical (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (i : Fin s.length) :
    evaluation s c D I J hdeg hD hs v hv hn
      (FiniteQuadraticTower.root ℚ[X][X]
        (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
          ⟨i.val, by simpa only [SplitRadicalCoordinateAlgebra.radicands, List.length_map,
            List.length_finRange] using i.isLt⟩) =
      (v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i)) : ℚ) := by
  rw [← SourceAffineChartCoordinates.specialization_radical s c D I J hs]
  change evaluation s c D I J hdeg hD hs v hv hn
    (SourceAffineChartCoordinates.specialization s c D I J hs
      (radical c D I J i : CoordinateRing c D I J)) = _
  rw [evaluation_specialization]
  exact SourceIntegerPointEvaluation.evaluation_coordinate c D I J hdeg hD v hv
    (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i))

theorem evaluation_base (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (P : ℚ[X][X]) :
    evaluation s c D I J hdeg hD hs v hv hn
      (algebraMap ℚ[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J) P) =
      P.evalEval (v (SourceIntegerPoints.affineIndex D hD 1) : ℚ)
        (v (SourceIntegerPoints.affineIndex D hD 0) : ℚ) := by
  let := BivariateQuadraticTowerPoints.scalarAlgebra
    (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
  have hh := BivariateQuadraticTowerPoints.base_evaluation
    (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)
    (evaluation s c D I J hdeg hD hs v hv hn).toRatAlgHom P
  simp only [RingHom.toRatAlgHom_apply] at hh
  rw [← native_specialization_variables.2.1, ← native_specialization_variables.1,
    evaluation_affine, evaluation_affine] at hh
  exact hh

include hdeg hs in
theorem rational_root_equation (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (i : Fin s.length) :
    (v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i)) : ℚ) ^ 2 =
      c i * (∏ a ∈ I i, ((v (SourceIntegerPoints.affineIndex D hD 1) : ℚ) + (a : ℚ))) *
        ∏ b ∈ J i, ((v (SourceIntegerPoints.affineIndex D hD 0) : ℚ) + (b : ℚ)) := by
  let idx : Fin (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J).length :=
    ⟨i.val, by simpa only [SplitRadicalCoordinateAlgebra.radicands, List.length_map,
      List.length_finRange] using i.isLt⟩
  have hget : (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J).get idx =
      ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i) := by
    change ((List.finRange s.length).map (fun j ↦
      ScaledSplitWordSquares.scaledPolynomial (c j) (I j) (J j)))[i.val] = _
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  have hh := congrArg (evaluation s c D I J hdeg hD hs v hv hn)
    (FiniteQuadraticTower.root_square ℚ[X][X]
      (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J) idx)
  rw [map_pow, evaluation_radical, hget, evaluation_base,
    SplitRadicalCoordinateAlgebra.equation_evaluation] at hh
  exact hh

include hdeg in
theorem integer_root_equation (cZ : Fin s.length → ℤ)
    (hsZ : ∀ i, s.get i = radicand (cZ i : ℚ)
      (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid (fun i ↦ (cZ i : ℚ)) D I J v)
    (hn : v (SourceIntegerPoints.normalizer D) = 1) (i : Fin s.length) :
    v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i)) ^ 2 =
      cZ i * SplitRadicalPointHeight.integerProduct (I i) (v (SourceIntegerPoints.affineIndex D hD 1)) *
        SplitRadicalPointHeight.integerProduct (J i) (v (SourceIntegerPoints.affineIndex D hD 0)) := by
  have hh := rational_root_equation s (fun i ↦ (cZ i : ℚ)) D I J hdeg hD hsZ v hv hn i
  unfold SplitRadicalPointHeight.integerProduct
  exact_mod_cast hh

include hs in
theorem radical_ne_zero (i : Fin s.length) : radical c D I J i ≠ 0 := by
  intro hz
  have hz' : (radical c D I J i : CoordinateRing c D I J) = 0 := congrArg Subtype.val hz
  have hh := congrArg (SourceAffineChartCoordinates.specialization s c D I J hs) hz'
  change SourceAffineChartCoordinates.specialization s c D I J hs
    (quotientMap c D I J (MvPolynomial.X (Sum.inr i))) =
      SourceAffineChartCoordinates.specialization s c D I J hs 0 at hh
  rw [SourceAffineChartCoordinates.specialization_radical, map_zero] at hh
  exact (QuadraticTowerRootBasis.roots_linearlyIndependent ℚ[X][X]
    (SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) c I J)).ne_zero _ hh

end SourceNativeIntegerPoint
