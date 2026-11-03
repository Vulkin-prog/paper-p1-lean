module

public import PaperP1.Algebra.HomogeneousChartCoefficientQuotient
public import PaperP1.Algebra.VeroneseCoordinateCharts

/-! # The actual source specializes to the affine quadratic tower with exactly kernel (Z-1) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSourceSpecialization

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalPresentation
  PaperP1.HomogeneousSplitRadicalFiniteVeronese PaperP1.HomogeneousSplitRadicalBaseInjection
  PaperP1.HomogeneousSplitRadicalChart PaperP1.VeroneseCoordinateCharts

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

theorem presentation_baseVariable (j : Fin 3) :
    presentationEquiv s c D I J hs (baseVariable c D I J j) =
      algebraMap (PolynomialRing F) (FiniteQuadraticTower.Tower (PolynomialRing F) s)
        (TrivariatePolynomialEquiv.threeEquiv F (MvPolynomial.X j)) := by
  have hx : basePolynomialMap c D I J (MvPolynomial.X j) = baseVariable c D I J j := by
    change quotientMap c D I J (MvPolynomial.rename Sum.inl (MvPolynomial.X j)) = _
    rw [MvPolynomial.rename_X]
    rfl
  rw [← hx, presentationEquiv_base]

def specialization : CoordinateRing c D I J →+* FiniteQuadraticTower.Tower F[X][X] (s.map (chart F)) :=
  (QuadraticTowerBaseChange.mapData (chart F) s).hom.comp (presentationEquiv s c D I J hs).toRingHom

theorem specialization_surjective : Function.Surjective (specialization s c D I J hs) :=
  (QuadraticTowerQuotient.map_surjective (chart F) (HomogeneousChartCoefficientQuotient.chart_surjective F) s).comp
    (presentationEquiv s c D I J hs).surjective

theorem specialization_ker : RingHom.ker (specialization s c D I J hs) =
    Ideal.span {baseVariable c D I J (2 : Fin 3) - 1} := by
  have he : (Ideal.span {baseVariable c D I J (2 : Fin 3) - 1}).map
      (presentationEquiv s c D I J hs).toRingHom =
      (RingHom.ker (chart F)).map
        (algebraMap (PolynomialRing F) (FiniteQuadraticTower.Tower (PolynomialRing F) s)) := by
    rw [HomogeneousChartCoefficientQuotient.chart_ker]
    simp only [Ideal.map_span, Set.image_singleton, map_sub, map_one]
    change Ideal.span {presentationEquiv s c D I J hs (baseVariable c D I J (2 : Fin 3)) - 1} = _
    rw [presentation_baseVariable, TrivariatePolynomialEquiv.threeEquiv_X_two]
  rw [specialization, ← RingHom.comap_ker, QuadraticTowerQuotient.map_ker, ← he]
  exact Ideal.comap_map_of_bijective (presentationEquiv s c D I J hs).toRingHom
    (presentationEquiv s c D I J hs).bijective

def quotientEquiv :
    (CoordinateRing c D I J) ⧸ Ideal.span {baseVariable c D I J (2 : Fin 3) - 1} ≃+*
      FiniteQuadraticTower.Tower F[X][X] (s.map (chart F)) :=
  (Ideal.quotEquivOfEq (specialization_ker s c D I J hs).symm).trans
    ((specialization s c D I J hs).quotientKerEquivOfSurjective
      (specialization_surjective s c D I J hs))

theorem quotientEquiv_mk (x : CoordinateRing c D I J) :
    quotientEquiv s c D I J hs (Ideal.Quotient.mk _ x) = specialization s c D I J hs x := by
  rw [quotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end PaperP1.HomogeneousSourceSpecialization
