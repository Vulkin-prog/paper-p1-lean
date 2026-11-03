module

public import PaperP1.Algebra.NativeVeroneseAffineIdeal
public import PaperP1.Algebra.GradedQuotientChartMap

/-! # The actual native Veronese prime-quotient chart is the affine plane equation quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeVeroneseQuotientChart

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.StandardVeroneseCoordinates PaperP1.NativeVeroneseAffineIdeal

local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance affineRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

variable (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) (Q : Ideal (Base F D))

local instance quotientRing : CommRing (Base F D ⧸ Q) := inferInstance
local instance quotientSemiring : Semiring (Base F D ⧸ Q) := (quotientRing F D Q).toSemiring
local instance quotientModule : Module F (Base F D ⧸ Q) := Algebra.toModule

variable (hQ : letI := SourceVeroneseGrading.nativeGrading F D hD
  Q.IsHomogeneous (SourceVeroneseGrading.nativePiece F D))

theorem chartIdeal_eq :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    (RingHom.ker (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).toRingHom).map
      ((NativeAffineChart.equiv F D hD).toRingHom.comp
        (GradedDehomogenization.map (SourceVeroneseGrading.nativePiece F D) (coordinatePower_mem F D 2))) =
      affineIdeal F D Q := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  have hk : RingHom.ker (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).toRingHom = Q :=
    Ideal.mk_ker
  have he : (NativeAffineChart.equiv F D hD).toRingHom.comp
      (GradedDehomogenization.map (SourceVeroneseGrading.nativePiece F D) (coordinatePower_mem F D 2)) =
      affineMap F D := by
    apply RingHom.ext
    intro p
    exact NativeAffineChart.equiv_dehomogenization F D hD p
  rw [hk, he]
  rfl

def equiv :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    Away (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
      (Ideal.Quotient.mk Q (coordinatePower F D 2)) ≃+* F[X][X] ⧸ affineIdeal F D Q := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  exact (GradedQuotientChartMap.transportEquiv
    (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q)
    (HomogeneousQuotientGrading.mk_surjective _ Q) (coordinatePower_mem F D 2)
    (NativeAffineChart.equiv F D hD)).trans (Ideal.quotEquivOfEq (chartIdeal_eq F D hD Q))

set_option backward.isDefEq.respectTransparency false in
theorem equiv_dehomogenization (p : Base F D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    equiv F D hD Q hQ
      (GradedDehomogenization.map (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).map_mem (coordinatePower_mem F D 2))
        (Ideal.Quotient.mk Q p)) = Ideal.Quotient.mk (affineIdeal F D Q) (affineMap F D p) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  have hn := DFunLike.congr_fun (GradedDehomogenization.map_natural
    (SourceVeroneseGrading.nativePiece F D) (coordinatePower_mem F D 2)
    (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q)) p
  calc
    _ = equiv F D hD Q hQ
        (Away.map (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q)
          (coordinatePower F D 2) (GradedDehomogenization.map (SourceVeroneseGrading.nativePiece F D)
            (coordinatePower_mem F D 2) p)) := congrArg (equiv F D hD Q hQ) hn.symm
    _ = _ := by
      have ht := GradedQuotientChartMap.transportEquiv_map
        (HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q)
        (HomogeneousQuotientGrading.mk_surjective _ Q) (coordinatePower_mem F D 2)
        (NativeAffineChart.equiv F D hD)
        (GradedDehomogenization.map (SourceVeroneseGrading.nativePiece F D) (coordinatePower_mem F D 2) p)
      have h := congrArg (Ideal.quotEquivOfEq (chartIdeal_eq F D hD Q)) ht
      exact h.trans (congrArg (Ideal.Quotient.mk (affineIdeal F D Q))
        (NativeAffineChart.equiv_dehomogenization F D hD p))

end PaperP1.NativeVeroneseQuotientChart
