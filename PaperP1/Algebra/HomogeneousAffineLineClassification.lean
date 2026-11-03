module

public import PaperP1.Algebra.HomogeneousLinearForm
public import PaperP1.Algebra.AffineLineClassification

/-! # The affine chart of a homogeneous linear image through a point has an exhaustive line classification -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousAffineLineClassification

open Polynomial PaperP1.NativeAffineChart PaperP1.TrivariatePolynomialEquiv

variable {F : Type*} [Field F]

def coefficient (f : MvPolynomial (Fin 3) F) (i : Fin 3) : F := f.coeff (Finsupp.single i 1)

theorem specialization_C (a : F) : specialization F (MvPolynomial.C a) = C (C a) := by
  change HomogeneousSplitRadicalChart.chart F (threeEquiv F (MvPolynomial.C a)) = _
  rw [HomogeneousSplitRadicalPolynomials.threeEquiv_C]
  simp [HomogeneousSplitRadicalChart.chart]

theorem specialization_Y : specialization F (MvPolynomial.X (0 : Fin 3)) = (X : F[X][X]) := by
  change HomogeneousSplitRadicalChart.chart F (threeEquiv F (MvPolynomial.X (0 : Fin 3))) = _
  rw [threeEquiv_X_zero]
  simp [HomogeneousSplitRadicalChart.chart]

theorem specialization_X : specialization F (MvPolynomial.X (1 : Fin 3)) = C (X : F[X]) := by
  change HomogeneousSplitRadicalChart.chart F (threeEquiv F (MvPolynomial.X (1 : Fin 3))) = _
  rw [threeEquiv_X_one]
  simp [HomogeneousSplitRadicalChart.chart]

theorem specialization_linear (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous 1) :
    specialization F f = AffineLineClassification.linear (coefficient f 0) (coefficient f 1) (coefficient f 2) := by
  calc
    _ = specialization F (MvPolynomial.C (coefficient f 0) * MvPolynomial.X 0 +
        MvPolynomial.C (coefficient f 1) * MvPolynomial.X 1 +
        MvPolynomial.C (coefficient f 2) * MvPolynomial.X 2) :=
      congrArg (specialization F) (HomogeneousLinearForm.eq_three f hf)
    _ = _ := by
      simp only [map_add, map_mul, specialization_C, specialization_Y, specialization_X,
        NativeVeroneseAffineIdeal.specialization_Z, mul_one, AffineLineClassification.linear]

theorem coefficients_nonzero (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous 1) (hf0 : f ≠ 0) :
    coefficient f 0 ≠ 0 ∨ coefficient f 1 ≠ 0 ∨ coefficient f 2 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hf0
  exact (HomogeneousLinearForm.eq_three f hf).trans (by
    change MvPolynomial.C (coefficient f 0) * _ + MvPolynomial.C (coefficient f 1) * _ +
      MvPolynomial.C (coefficient f 2) * _ = 0
    rw [h.1, h.2.1, h.2.2]
    simp)

theorem classify (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous 1) (hf0 : f ≠ 0)
    (x y : F) (hpoint : AffineLineClassification.valueMap x y (specialization F f) = 0) :
    (∃ α β : F, Ideal.span {specialization F f} = Ideal.span {NativeVeroneseLineChart.equation α β} ∧
      y = α * x + β) ∨
    Ideal.span {specialization F f} = Ideal.span {NativeVeroneseVerticalChart.equation x} := by
  have hlinear := specialization_linear f hf
  have hzero := (AffineLineClassification.value_linear
    (coefficient f 0) (coefficient f 1) (coefficient f 2) x y).symm.trans
      ((congrArg (AffineLineClassification.valueMap x y) hlinear).symm.trans hpoint)
  exact hlinear ▸ AffineLineClassification.classify
    (coefficient f 0) (coefficient f 1) (coefficient f 2) x y (coefficients_nonzero f hf hf0) hzero

end PaperP1.HomogeneousAffineLineClassification
