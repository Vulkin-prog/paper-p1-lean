module

public import PaperP1.Algebra.HomogeneousChartCoefficientQuotient
public import PaperP1.Algebra.VeroneseCoordinateCharts

/-! # The actual native Veronese Z-chart is the affine polynomial plane -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeAffineChart

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalChart
  PaperP1.TrivariatePolynomialEquiv PaperP1.StandardVeroneseCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

local instance sourceRing (F : Type*) [Field F] : CommRing (HomogeneousSplitRadicalData.PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

def specialization (F : Type*) [Field F] : MvPolynomial (Fin 3) F →+* F[X][X] :=
  (chart F).comp (threeEquiv F).toRingHom

theorem specialization_surjective (F : Type*) [Field F] : Function.Surjective (specialization F) :=
  (HomogeneousChartCoefficientQuotient.chart_surjective F).comp (threeEquiv F).surjective

theorem specialization_ker (F : Type*) [Field F] :
    RingHom.ker (specialization F) = Ideal.span {(MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) F) - 1} := by
  have he : (Ideal.span {(MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) F) - 1}).map
      (threeEquiv F).toRingHom = RingHom.ker (chart F) := by
    rw [HomogeneousChartCoefficientQuotient.chart_ker]
    simp only [Ideal.map_span, Set.image_singleton, map_sub, map_one]
    change Ideal.span {threeEquiv F (MvPolynomial.X (2 : Fin 3)) - 1} = _
    rw [threeEquiv_X_two]
  rw [specialization, ← RingHom.comap_ker, ← he]
  exact Ideal.comap_map_of_bijective (threeEquiv F).toRingHom (threeEquiv F).bijective

def quotientEquiv (F : Type*) [Field F] :
    (MvPolynomial (Fin 3) F) ⧸ Ideal.span {(MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) F) - 1} ≃+*
      F[X][X] :=
  (Ideal.quotEquivOfEq (specialization_ker F).symm).trans
    ((specialization F).quotientKerEquivOfSurjective (specialization_surjective F))

theorem quotientEquiv_mk (F : Type*) [Field F] (p : MvPolynomial (Fin 3) F) :
    quotientEquiv F (Ideal.Quotient.mk _ p) = specialization F p := by
  rw [quotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

def originalEquiv (F : Type*) [Field F] :
    Away (MvPolynomial.homogeneousSubmodule (Fin 3) F) (MvPolynomial.X (2 : Fin 3)) ≃+* F[X][X] :=
  (GradedDehomogenizationQuotient.equiv (MvPolynomial.homogeneousSubmodule (Fin 3) F)
    (MvPolynomial.isHomogeneous_X F (2 : Fin 3))).symm.trans (quotientEquiv F)

set_option backward.isDefEq.respectTransparency false in
theorem originalEquiv_dehomogenization (F : Type*) [Field F] (p : MvPolynomial (Fin 3) F) :
    originalEquiv F
        (GradedDehomogenization.map (MvPolynomial.homogeneousSubmodule (Fin 3) F)
          (MvPolynomial.isHomogeneous_X F (2 : Fin 3)) p) = specialization F p := by
  change quotientEquiv F
    ((GradedDehomogenizationQuotient.equiv (MvPolynomial.homogeneousSubmodule (Fin 3) F)
      (MvPolynomial.isHomogeneous_X F (2 : Fin 3))).symm
        (GradedDehomogenization.map (MvPolynomial.homogeneousSubmodule (Fin 3) F)
          (MvPolynomial.isHomogeneous_X F (2 : Fin 3)) p)) = _
  rw [← GradedDehomogenizationQuotient.equiv_mk, RingEquiv.symm_apply_apply]
  exact quotientEquiv_mk F p

def equiv (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    Away (SourceVeroneseGrading.nativePiece F D) (coordinatePower F D 2) ≃+* F[X][X] := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  exact (VeroneseCoordinateCharts.nativeEquiv F D hD 2).trans (originalEquiv F)

theorem equiv_dehomogenization (F : Type*) [Field F] (D : ℕ) (hD : 0 < D)
    (p : HomogeneousSplitRadicalVeroneseTowerData.Base F D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    equiv F D hD (GradedDehomogenization.map (SourceVeroneseGrading.nativePiece F D)
      (coordinatePower_mem F D 2) p) = specialization F (p : MvPolynomial (Fin 3) F) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  exact (congrArg (originalEquiv F)
    (GradedVeroneseChart.map_dehomogenization (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD
      (MvPolynomial.isHomogeneous_X F (2 : Fin 3)) p)).trans
        (originalEquiv_dehomogenization F p)

end PaperP1.NativeAffineChart
