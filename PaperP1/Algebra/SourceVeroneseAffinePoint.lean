module

public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Algebra.SourceCurveQuotient
public import PaperP1.Algebra.AffineLineClassification

/-! # Actual affine source points restrict to source-Veronese points and their curve images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseAffinePoint

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

def sourceMap (ψ : SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J →+* F) :
    HomogeneousSplitRadicalVeronese.veronese c D I J →+* F :=
  ψ.comp ((SourceAffineChartCoordinates.specialization s c D I J hs).comp
    (HomogeneousSplitRadicalVeronese.veronese c D I J).val.toRingHom)

variable (ψ : SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J →+* F)
  (x y : F)
  (hψ : ∀ t : F[X][X], ψ (algebraMap F[X][X]
    (SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) c I J) t) = t.evalEval x y)
  (hD : 0 < D)

include hψ in
theorem sourceMap_base (a : Base F D) :
    sourceMap s c D I J hs ψ (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs a) =
      AffineLineClassification.valueMap x y (NativeVeroneseAffineIdeal.affineMap F D a) := by
  change ψ (SourceAffineChartCoordinates.specialization s c D I J hs
    (HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J (a : MvPolynomial (Fin 3) F))) = _
  rw [SourceAffineChartCoordinates.specialization_base, hψ]
  exact congrArg (fun f : F[X][X] →+* F ↦ f (NativeVeroneseAffineIdeal.affineMap F D a))
    (congrFun (Polynomial.evalEvalRingHom_eq x) y)

include hψ in
theorem curve_image (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
    (hcurve : P ≤ RingHom.ker (sourceMap s c D I J hs ψ)) :
    NativeVeroneseAffineIdeal.affineIdeal F D (SourceCurveQuotient.baseIdeal s c D I J hs hD P) ≤
      RingHom.ker (AffineLineClassification.valueMap x y) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs a ∈ P at ha
  change AffineLineClassification.valueMap x y (NativeVeroneseAffineIdeal.affineMap F D a) = 0
  rw [← sourceMap_base s c D I J hs ψ x y hψ hD]
  exact RingHom.mem_ker.mp (hcurve ha)

end PaperP1.SourceVeroneseAffinePoint
