module

public import PaperP1.Geometry.IntegerCoefficientProjectivePoint
public import PaperP1.Geometry.GradedFieldChartEvaluation

/-! # An actual Spec-field morphism for every nonzero integer projective coefficient point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCoefficientProjectiveMorphism

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]

def evaluation (a : σ → K) : MvPolynomial σ ℤ →+* K := eval₂Hom (Int.castRingHom K) a

theorem evaluation_X (a : σ → K) (i : σ) : evaluation a (X i) = a i := by
  simp [evaluation]

def map (a : σ → K) (i : σ) (hi : a i ≠ 0) :
    Spec (CommRingCat.of K) ⟶ Proj (homogeneousSubmodule σ ℤ) :=
  GradedFieldChartEvaluation.pointMap (homogeneousSubmodule σ ℤ) (evaluation a)
    (by simpa only [evaluation_X] using hi) (isHomogeneous_X ℤ i)

theorem map_closedPoint (a : σ → K) (ha : a ≠ 0) (i : σ) (hi : a i ≠ 0) :
    map a i hi (IsLocalRing.closedPoint K) = IntegerCoefficientProjectivePoint.point a ha := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n P hP
  rw [IntegerCoefficientProjectivePoint.homogeneous_mem_iff _ _ _ hP]
  change P ∈ (GradedFieldChartEvaluation.pointMap (homogeneousSubmodule σ ℤ) (evaluation a)
    _ (isHomogeneous_X ℤ i) (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔ _
  exact (GradedFieldChartEvaluation.pointMap_homogeneous_mem (homogeneousSubmodule σ ℤ)
    (evaluation a) (by simpa only [evaluation_X] using hi) (isHomogeneous_X ℤ i) P hP).trans
      (by rw [eval_map]; rfl)

end PaperP1.IntegerCoefficientProjectiveMorphism
