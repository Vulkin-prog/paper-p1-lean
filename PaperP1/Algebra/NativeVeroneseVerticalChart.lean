module

public import PaperP1.Algebra.NativeVeroneseQuotientChart
public import PaperP1.Algebra.SquareLineMatching

/-! # The actual base-curve chart over a vertical line and its literal radical polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeVeroneseVerticalChart

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.StandardVeroneseCoordinates PaperP1.NativeVeroneseAffineIdeal

local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance affineRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

variable {F : Type*} [Field F]

def equation (γ : F) : F[X][X] := C (X - C γ)

def polynomialMap (γ : F) : F[X][X] →+* F[X] := mapRingHom (evalRingHom γ)

theorem polynomialMap_kernel (γ : F) : RingHom.ker (polynomialMap γ) = Ideal.span {equation γ} := by
  simp only [polynomialMap, ker_mapRingHom, ker_evalRingHom, Ideal.map_span, Set.image_singleton, equation]

theorem polynomialMap_surjective (γ : F) : Function.Surjective (polynomialMap γ) := by
  apply Polynomial.map_surjective
  intro a
  exact ⟨C a, by simp⟩

def polynomialEquiv (γ : F) : F[X][X] ⧸ Ideal.span {equation γ} ≃+* F[X] :=
  (Ideal.quotEquivOfEq (polynomialMap_kernel γ).symm).trans
    ((polynomialMap γ).quotientKerEquivOfSurjective (polynomialMap_surjective γ))

theorem polynomialEquiv_mk (γ : F) (p : F[X][X]) :
    polynomialEquiv γ (Ideal.Quotient.mk _ p) = polynomialMap γ p := by
  rw [polynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem polynomialMap_scaled (γ c : F) (I J : Finset ℤ) :
    polynomialMap γ (ScaledSplitWordSquares.scaledPolynomial c I J) =
      C c * C ((FormalWordPolynomials.linearOver F I).eval γ) * FormalWordPolynomials.linearOver F J := by
  have he : (evalRingHom γ).comp (C : F →+* F[X]) = RingHom.id F := by
    apply RingHom.ext
    intro a
    exact eval_C
  change (ScaledSplitWordSquares.scaledPolynomial c I J).map (evalRingHom γ) = _
  simp only [ScaledSplitWordSquares.scaledPolynomial, FormalWordPolynomials.wordOver,
    Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom, eval_C, Polynomial.map_map, he, Polynomial.map_id]
  exact (mul_assoc _ _ _).symm

variable (D : ℕ) (hD : 0 < D) (Q : Ideal (Base F D))

local instance quotientRing : CommRing (Base F D ⧸ Q) := inferInstance
local instance quotientSemiring : Semiring (Base F D ⧸ Q) := (quotientRing D Q).toSemiring
local instance quotientModule : Module F (Base F D ⧸ Q) := Algebra.toModule

variable (hQ : letI := SourceVeroneseGrading.nativeGrading F D hD
    Q.IsHomogeneous (SourceVeroneseGrading.nativePiece F D)) (γ : F)
  (hline : affineIdeal F D Q = Ideal.span {equation γ})

include hline in
theorem coordinate_ne_zero : Ideal.Quotient.mk Q (coordinatePower F D 2) ≠ 0 := by
  intro hzero
  have hm := Ideal.mem_map_of_mem (affineMap F D) (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have he : affineMap F D (coordinatePower F D 2) = 1 := by
    rw [affineMap_apply, coordinatePower_val, map_pow, specialization_Z, one_pow]
  have h1 : (1 : F[X][X]) ∈ Ideal.span {equation γ} := hline ▸ he ▸ hm
  have hz := RingHom.mem_ker.mp ((polynomialMap_kernel γ).symm ▸ h1)
  exact one_ne_zero (by simpa only [map_one] using hz)

def equiv :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    Away (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
      (Ideal.Quotient.mk Q (coordinatePower F D 2)) ≃+* F[X] := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  exact (NativeVeroneseQuotientChart.equiv F D hD Q hQ).trans
    ((Ideal.quotEquivOfEq hline).trans (polynomialEquiv γ))

theorem equiv_dehomogenization (p : Base F D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    equiv D hD Q hQ γ hline
      (GradedDehomogenization.map (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).map_mem (coordinatePower_mem F D 2))
        (Ideal.Quotient.mk Q p)) = polynomialMap γ (affineMap F D p) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  have h := congrArg ((Ideal.quotEquivOfEq hline).trans (polynomialEquiv γ))
    (NativeVeroneseQuotientChart.equiv_dehomogenization F D hD Q hQ p)
  exact h.trans (polynomialEquiv_mk γ (affineMap F D p))

theorem equiv_radicand (c : F) (I J : Finset ℤ) (hdeg : I.card + J.card ≤ 2 * D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    equiv D hD Q hQ γ hline
      (GradedDehomogenization.map (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).map_mem (coordinatePower_mem F D 2))
        (Ideal.Quotient.mk Q (baseRadicand c D I J hdeg))) =
      C c * C ((FormalWordPolynomials.linearOver F I).eval γ) * FormalWordPolynomials.linearOver F J := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  exact (equiv_dehomogenization D hD Q hQ γ hline _).trans
    ((congrArg (polynomialMap γ) (affineMap_radicand c D I J hdeg)).trans (polynomialMap_scaled γ c I J))

end PaperP1.NativeVeroneseVerticalChart
