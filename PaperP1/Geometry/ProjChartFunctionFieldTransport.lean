module

public import PaperP1.Geometry.ProjChartFunctionField
public import Mathlib.Algebra.Group.Even

/-! # An actual chart isomorphism transports the projective function field and its squares -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjChartFunctionFieldTransport

open AlgebraicGeometry HomogeneousLocalization

variable {A σ R : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing R] (G : ℕ → σ) [GradedRing G]
  (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0)
  (e : Away G b ≃+* R)

def equiv :
    letI := ProjIntegral.integral G hpos
    (Proj G).functionField ≃+* FractionRing R := by
  let := ProjIntegral.integral G hpos
  letI : Algebra (Away G b) (Proj G).functionField := (ProjChartFunctionField.chartMap G hpos hb0).toAlgebra
  letI := ProjChartFunctionField.chart_isFractionRing G hpos hb0 hb
  exact IsFractionRing.ringEquivOfRingEquiv e

theorem equiv_chartMap (x : Away G b) :
    letI := ProjIntegral.integral G hpos
    equiv G hpos hb hb0 e (ProjChartFunctionField.chartMap G hpos hb0 x) =
      algebraMap R (FractionRing R) (e x) := by
  let := ProjIntegral.integral G hpos
  let : Algebra (Away G b) (Proj G).functionField := (ProjChartFunctionField.chartMap G hpos hb0).toAlgebra
  let := ProjChartFunctionField.chart_isFractionRing G hpos hb0 hb
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e x

include hb in
theorem isSquare_iff (x : Away G b) :
    letI := ProjIntegral.integral G hpos
    IsSquare (ProjChartFunctionField.chartMap G hpos hb0 x) ↔
      IsSquare (algebraMap R (FractionRing R) (e x)) := by
  let := ProjIntegral.integral G hpos
  constructor
  · intro h
    simpa only [equiv_chartMap G hpos hb hb0 e] using h.map (equiv G hpos hb hb0 e)
  · intro h
    rw [← equiv_chartMap G hpos hb hb0 e x] at h
    simpa only [RingEquiv.symm_apply_apply] using h.map (equiv G hpos hb hb0 e).symm

end PaperP1.ProjChartFunctionFieldTransport
