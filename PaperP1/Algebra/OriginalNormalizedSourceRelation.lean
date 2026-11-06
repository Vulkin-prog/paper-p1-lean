module

public import PaperP1.Arithmetic.IntegerProjectedModelNormalization
public import PaperP1.Algebra.IntegralProjectedEquationReduction
public import PaperP1.Algebra.AffinePowerProjectionImage

/-! # The actual original normalized integer projected equation vanishes at the same chosen source coordinate

The original integral primitive coordinate and power parameters are identified
with the literal affine image coordinates. The original rational kernel and
scalar-multiple integer model imply the normalized affine source relation over
every field. Good-prime monicity, irreducibility, exact degree and coefficient
bounds are assembled for that same original equation and source element.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.OriginalNormalizedSourceRelation
open Polynomial Finset PaperP1.IntegralSplitRadicalModel PaperP1.IntegralSourceProjectionCoordinates
open PaperP1.SourceProjectiveEmbedding
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarTower
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

section General
variable (F : Type*) [Field F] (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ)
  (u : GeneratorIndex ℚ (Fin k) D → ℕ)

def fieldPrimitive : PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) (fun i ↦ (c i : F)) I J :=
  sourceMap F (List.finRange k) c I J (integralPrimitive k D c I J u)

theorem fieldCoordinates (i : Fin 4) :
    sourceMap F (List.finRange k) c I J (integralCoordinates k D c I J u i) =
      ((Fin.snoc (Fin.cons (fieldPrimitive F k D c I J u)
        (PaperP1.AffinePowerProjectionImage.parameters F D
          (PaperP1.SplitRadicalCoordinateAlgebra.radicands (List.finRange k) (fun i ↦ (c i : F)) I J))) 1) :
        Fin 4 → PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) (fun i ↦ (c i : F)) I J) i := by
  fin_cases i
  · rfl
  · change sourceMap F (List.finRange k) c I J
      ((algebraMap ℤ[X][X] (Source (List.finRange k) c I J) X)^D) =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) (fun i ↦ (c i : F)) I J) (X^D)
    rw [map_pow, sourceMap_base, coefficientMap_X, map_pow]
  · change sourceMap F (List.finRange k) c I J
      ((algebraMap ℤ[X][X] (Source (List.finRange k) c I J) (C X))^D) =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) (fun i ↦ (c i : F)) I J) ((C X)^D)
    rw [map_pow, sourceMap_base, coefficientMap_C_X, map_pow]
  · change sourceMap F (List.finRange k) c I J 1 = 1
    exact map_one _

theorem normalized_relation (Q : MvPolynomial (Fin 4) ℤ) (b : ℤ)
    (hQ : MvPolynomial.eval₂ (Int.castRingHom
        (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange k) (fun i ↦ (c i : F)) I J))
      (fun i ↦ sourceMap F (List.finRange k) c I J (integralCoordinates k D c I J u i)) Q = 0) :
    letI := PaperP1.LocalizedAffineQuadraticSource.sourceAlgebra F D
      (PaperP1.SplitRadicalCoordinateAlgebra.radicands (List.finRange k) (fun i ↦ (c i : F)) I J)
    Polynomial.aeval (fieldPrimitive F k D c I J u)
      (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized F Q b)) = 0 := by
  let s := PaperP1.SplitRadicalCoordinateAlgebra.radicands (List.finRange k) (fun i ↦ (c i : F)) I J
  let y : (PaperP1.LocalizedAffineQuadraticSource.Source F s) := fieldPrimitive F k D c I J u
  let v : Fin 2 → (PaperP1.LocalizedAffineQuadraticSource.Source F s) := PaperP1.AffinePowerProjectionImage.parameters F D s
  let ξ : Fin 4 → (PaperP1.LocalizedAffineQuadraticSource.Source F s) := Fin.snoc (Fin.cons y v) 1
  have hcoords : (fun i ↦ sourceMap F (List.finRange k) c I J (integralCoordinates k D c I J u i)) = ξ :=
    funext (fieldCoordinates F k D c I J u)
  have hmapped : MvPolynomial.aeval (R := F) ξ (MvPolynomial.map (Int.castRingHom F) Q) = 0 := by
    rw [← PaperP1.IntegerSourcePolynomialRelations.integer_evaluation_eq_mapped_aeval (F := F)]
    rw [← hcoords]
    exact hQ
  have hnorm : MvPolynomial.aeval (R := F) ξ (PaperP1.IntegerProjectedModelNormalization.normalized F Q b) = 0 := by
    rw [PaperP1.IntegerProjectedModelNormalization.normalized, map_mul, hmapped, mul_zero]
  let := PaperP1.LocalizedAffineQuadraticSource.sourceAlgebra F D s
  have hc : algebraMap (MvPolynomial (Fin 2) F) (PaperP1.LocalizedAffineQuadraticSource.Source F s) = (MvPolynomial.aeval v).toRingHom := by
    change (PaperP1.AffinePowerProjectionImage.parameterMap F D s).toRingHom = _
    exact congrArg AlgHom.toRingHom (PaperP1.AffinePowerProjectionImage.parameterMap_evaluation F D s)
  change Polynomial.eval₂ (algebraMap (MvPolynomial (Fin 2) F) (PaperP1.LocalizedAffineQuadraticSource.Source F s)) y
    (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized F Q b)) = 0
  rw [hc]
  exact (PaperP1.MonicP3LastChart.evaluation (PaperP1.IntegerProjectedModelNormalization.normalized F Q b) v y).trans hnorm

end General

section Original
variable (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ))
  (c : Fin s.length → ℤ) (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : ℚ)
    (2*D-((I i).card+(J i).card)) (I i) (J i))
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

theorem original_model_relation (q : MvPolynomial (Fin 4) ℚ)
    (hideal : PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q})
    (a : ℚ) (Q : MvPolynomial (Fin 4) ℤ)
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (b : ℤ) (F : Type*) [Field F] :
    letI := PaperP1.LocalizedAffineQuadraticSource.sourceAlgebra F D
      (PaperP1.SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) (fun i ↦ (c i : F)) I J)
    Polynomial.aeval (fieldPrimitive F s.length D c I J u)
      (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized F Q b)) = 0 := by
  apply normalized_relation F s.length D c I J u Q b
  exact PaperP1.IntegralProjectedEquationReduction.original_model_reduces s c D hD I J hs u
    q hideal a Q hmodel F

theorem original_good_prime_data (q : MvPolynomial (Fin 4) ℚ)
    (hideal : PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q})
    (hq : q.IsHomogeneous (2 ^ s.length * D ^ 2)) (hm : (MvPolynomial.finSuccEquiv ℚ 3 q).Monic)
    (a : ℚ) (ha : a ≠ 0) (Q : MvPolynomial (Fin 4) ℤ)
    (hQ : Q.IsHomogeneous (2 ^ s.length * D ^ 2))
    (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (z : ℤ) (hz : PaperP1.P3UniversalGoodReduction.Certificate Q z)
    (p : ℕ) (hp : p.Prime) (hnotz : ¬ (p : ℤ) ∣ z)
    (hnotb : ¬ (p : ℤ) ∣ PaperP1.IntegerProjectedModelNormalization.topCoefficient Q (2 ^ s.length * D ^ 2)) :
    letI : Fact p.Prime := ⟨hp⟩
    let P := PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q
      (PaperP1.IntegerProjectedModelNormalization.topCoefficient Q (2 ^ s.length * D ^ 2)))
    letI := PaperP1.LocalizedAffineQuadraticSource.sourceAlgebra (ZMod p) D
      (PaperP1.SplitRadicalCoordinateAlgebra.radicands (List.finRange s.length) (fun i ↦ (c i : ZMod p)) I J)
    P.Monic ∧ P.natDegree = 2 ^ s.length * D ^ 2 ∧ Irreducible P ∧
      (∀ i, (P.coeff i).totalDegree ≤ 2 ^ s.length * D ^ 2) ∧
      Polynomial.aeval (fieldPrimitive (ZMod p) s.length D c I J u) P = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : 0 < 2 ^ s.length * D ^ 2 := by positivity
  have hh := PaperP1.IntegerProjectedModelNormalization.good_prime_affine_properties
    (2 ^ s.length * D ^ 2) hd Q hQ q a ha hq hm hmodel z hz p hp hnotz hnotb
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, ?_⟩
  exact original_model_relation s c D hD I J hs u q hideal a Q hmodel
    (PaperP1.IntegerProjectedModelNormalization.topCoefficient Q (2 ^ s.length * D ^ 2)) (ZMod p)
end Original

end PaperP1.OriginalNormalizedSourceRelation
