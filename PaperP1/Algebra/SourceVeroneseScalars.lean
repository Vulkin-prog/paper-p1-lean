module

public import PaperP1.Algebra.SourceVeroneseGradedBaseMap
public import PaperP1.Algebra.HomogeneousSplitRadicalVeroneseTowerData

/-! # The literal standard base inclusion preserves coefficient scalars -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseScalars

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.HomogeneousSplitRadicalBaseInjection

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

theorem standardBaseMap_commutes {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (a : F) :
    standardBaseMap s c D hD I J hs (algebraMap F (Base F D) a) =
      algebraMap F (HomogeneousSplitRadicalVeronese.veronese c D I J) a := by
  apply Subtype.ext
  change basePolynomialMap c D I J (algebraMap F (MvPolynomial (Fin 3) F) a) =
    algebraMap F (CoordinateRing c D I J) a
  exact (basePolynomialMap c D I J).commutes a

def standardBaseAlgHom {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Base F D →ₐ[F] HomogeneousSplitRadicalVeronese.veronese c D I J where
  __ := standardBaseMap s c D hD I J hs
  commutes' := standardBaseMap_commutes s c D hD I J hs

end PaperP1.SourceVeroneseScalars
