module

public import PaperP1.Algebra.IntegerSourcePolynomialRelations
public import PaperP1.Algebra.IntegralSourceProjectionCoordinates

/-! # The original chosen projected integer equation is an actual integral source relation and reduces to every field

The hypothesis is membership in the existing rational image kernel, or its
proved principal equation and an exact integer scalar-multiple model. No
positive-characteristic vanishing, monicity or point count is assumed.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegralProjectedEquationReduction
open Polynomial Finset IntegralSplitRadicalModel IntegralSplitRadicalReduction
open IntegralSourceProjectionCoordinates SourceProjectiveEmbedding IntegerSourcePolynomialRelations
open scoped Classical

section Original
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

variable (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ))
  (c : Fin s.length → ℤ) (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : ℚ)
    (2*D-((I i).card+(J i).card)) (I i) (J i))
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

theorem original_equation_integral (Q : MvPolynomial (Fin 4) ℤ)
    (hQ : MvPolynomial.map (Int.castRingHom ℚ) Q ∈ PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u)) :
    MvPolynomial.eval₂ (Int.castRingHom (Source (List.finRange s.length) c I J))
      (integralCoordinates s.length D c I J u) Q = 0 := by
  let V := PaperP1.HomogeneousSplitRadicalVeronese.veronese (fun i ↦ (c i : ℚ)) D I J
  let ξ : Fin 4 → V := PaperP1.LinearHypersurfaceImage.coordinates
    (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
    (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u)
  let Φ := (PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : ℚ)) D I J hs).comp V.val.toRingHom
  have hroot : MvPolynomial.eval₂ (Int.castRingHom V) ξ Q = 0 := by
    rw [integer_evaluation_eq_mapped_aeval (F := ℚ)]
    exact hQ
  have hΦ (a : V) : Φ a = PaperP1.SourceAffineChartCoordinates.specialization s
      (fun i ↦ (c i : ℚ)) D I J hs (a : PaperP1.HomogeneousSplitRadicalGrading.CoordinateRing (fun i ↦ (c i : ℚ)) D I J) := rfl
  have hcoords (i : Fin 4) : sourceMap ℚ (List.finRange s.length) c I J
      (integralCoordinates s.length D c I J u i) = Φ (ξ i) := by
    rw [hΦ]
    have hh := coordinates_compatibility s c D hD I J hs u i
    rw [fieldIndex_self] at hh
    simpa only [Equiv.refl_symm, Equiv.refl_apply] using hh
  have hh := map_integer_evaluation Φ ξ Q
  rw [hroot, map_zero] at hh
  have hfun : (fun i ↦ sourceMap ℚ (List.finRange s.length) c I J
      (integralCoordinates s.length D c I J u i)) = (fun i ↦ Φ (ξ i)) := funext hcoords
  have hQQ : MvPolynomial.eval₂ (Int.castRingHom
      (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : ℚ)) I J))
      (fun i ↦ sourceMap ℚ (List.finRange s.length) c I J (integralCoordinates s.length D c I J u i)) Q = 0 := by
    rw [hfun]
    exact hh.symm
  apply sourceMap_injective ℚ (List.finRange s.length) c I J
  rw [map_zero, map_integer_evaluation]
  exact hQQ

theorem original_equation_reduces (Q : MvPolynomial (Fin 4) ℤ)
    (hQ : MvPolynomial.map (Int.castRingHom ℚ) Q ∈ PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u))
    (F : Type*) [Field F] :
    MvPolynomial.eval₂ (Int.castRingHom
      (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : F)) I J))
      (fun i ↦ sourceMap F (List.finRange s.length) c I J (integralCoordinates s.length D c I J u i)) Q = 0 := by
  have hh := congrArg (sourceMap F (List.finRange s.length) c I J)
    (original_equation_integral s c D hD I J hs u Q hQ)
  rw [map_integer_evaluation, map_zero] at hh
  exact hh

theorem original_model_reduces (q : MvPolynomial (Fin 4) ℚ)
    (hideal : PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q})
    (a : ℚ) (Q : MvPolynomial (Fin 4) ℤ) (hmodel : MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q)
    (F : Type*) [Field F] :
    MvPolynomial.eval₂ (Int.castRingHom
      (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : F)) I J))
      (fun i ↦ sourceMap F (List.finRange s.length) c I J (integralCoordinates s.length D c I J u i)) Q = 0 := by
  apply original_equation_reduces s c D hD I J hs u Q ?_ F
  rw [hmodel]
  have hq : q ∈ PaperP1.LinearHypersurfaceImage.ideal
      (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
      (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) := by
    rw [hideal]
    exact Ideal.mem_span_singleton_self q
  exact Ideal.mul_mem_left _ _ hq

end Original
end PaperP1.IntegralProjectedEquationReduction
