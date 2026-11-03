module

public import PaperP1.Algebra.NativeVeroneseQuotientChart
public import PaperP1.Algebra.SquareLineMatching

/-! # The actual base-curve chart over an affine graph line and its literal radical polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeVeroneseLineChart

open Polynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.StandardVeroneseCoordinates PaperP1.NativeVeroneseAffineIdeal

local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance affineRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

variable {F : Type*} [Field F]

def equation (α β : F) : F[X][X] := X - C (C α * X + C β)

def polynomialMap (α β : F) : F[X][X] →+* F[X] := evalRingHom (C α * X + C β)

def polynomialEquiv (α β : F) : F[X][X] ⧸ Ideal.span {equation α β} ≃+* F[X] :=
  (quotientSpanXSubCAlgEquiv (C α * X + C β)).toRingEquiv

theorem polynomialEquiv_mk (α β : F) (p : F[X][X]) :
    polynomialEquiv α β (Ideal.Quotient.mk _ p) = polynomialMap α β p := rfl

theorem polynomialMap_scaled (α β c : F) (I J : Finset ℤ) :
    polynomialMap α β (ScaledSplitWordSquares.scaledPolynomial c I J) =
      SquareLineMatching.lineRestriction c I J α β := by
  change (ScaledSplitWordSquares.scaledPolynomial c I J).eval (C α * X + C β) = _
  simp only [ScaledSplitWordSquares.scaledPolynomial, FormalWordPolynomials.wordOver,
    eval_mul, eval_C, eval_map]
  change C c * (FormalWordPolynomials.linearOver F I *
    (FormalWordPolynomials.linearOver F J).comp (C α * X + C β)) = _
  exact (mul_assoc _ _ _).symm

variable (D : ℕ) (hD : 0 < D) (Q : Ideal (Base F D))

local instance quotientRing : CommRing (Base F D ⧸ Q) := inferInstance
local instance quotientSemiring : Semiring (Base F D ⧸ Q) := (quotientRing D Q).toSemiring
local instance quotientModule : Module F (Base F D ⧸ Q) := Algebra.toModule

variable (hQ : letI := SourceVeroneseGrading.nativeGrading F D hD
    Q.IsHomogeneous (SourceVeroneseGrading.nativePiece F D)) (α β : F)
  (hline : affineIdeal F D Q = Ideal.span {equation α β})

include hline in
theorem coordinate_ne_zero : Ideal.Quotient.mk Q (coordinatePower F D 2) ≠ 0 := by
  intro hzero
  have hm := Ideal.mem_map_of_mem (affineMap F D) (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have he : affineMap F D (coordinatePower F D 2) = 1 := by
    rw [affineMap_apply, coordinatePower_val, map_pow, specialization_Z, one_pow]
  have h1 : (1 : F[X][X]) ∈ Ideal.span {equation α β} := by
    exact hline ▸ he ▸ hm
  have hk : Ideal.span {equation α β} ≤ RingHom.ker (polynomialMap α β) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [polynomialMap, equation]
  have hz := RingHom.mem_ker.mp (hk h1)
  exact one_ne_zero (by simpa only [map_one] using hz)

def equiv :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    Away (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
      (Ideal.Quotient.mk Q (coordinatePower F D 2)) ≃+* F[X] := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  exact (NativeVeroneseQuotientChart.equiv F D hD Q hQ).trans
    ((Ideal.quotEquivOfEq hline).trans (polynomialEquiv α β))

theorem equiv_dehomogenization (p : Base F D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    equiv D hD Q hQ α β hline
      (GradedDehomogenization.map (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).map_mem (coordinatePower_mem F D 2))
        (Ideal.Quotient.mk Q p)) = polynomialMap α β (affineMap F D p) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  have h := congrArg ((Ideal.quotEquivOfEq hline).trans (polynomialEquiv α β))
    (NativeVeroneseQuotientChart.equiv_dehomogenization F D hD Q hQ p)
  exact h

theorem equiv_radicand (c : F) (I J : Finset ℤ) (hdeg : I.card + J.card ≤ 2 * D) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    letI := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
    equiv D hD Q hQ α β hline
      (GradedDehomogenization.map (HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) Q)
        ((HomogeneousQuotientGrading.mk (SourceVeroneseGrading.nativePiece F D) Q).map_mem (coordinatePower_mem F D 2))
        (Ideal.Quotient.mk Q (baseRadicand c D I J hdeg))) =
      SquareLineMatching.lineRestriction c I J α β := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) Q hQ
  exact (equiv_dehomogenization D hD Q hQ α β hline _).trans
    ((congrArg (polynomialMap α β) (affineMap_radicand c D I J hdeg)).trans
      (polynomialMap_scaled α β c I J))

end PaperP1.NativeVeroneseLineChart
