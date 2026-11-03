module

public import PaperP1.Geometry.ProjChartFunctionField

/-! # A concrete homogeneous chart identifies the actual projective function field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v w

namespace PaperP1.ProjAffineFieldEquiv

open AlgebraicGeometry HomogeneousLocalization

variable {A σ : Type u} {R : Type v} {L : Type w}
  [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0)
  [CommRing R] [CommRing L] [Algebra R L] [IsFractionRing R L] (e : Away G b ≃+* R)

def equiv :
    letI := ProjIntegral.integral G hG
    (Proj G).functionField ≃+* L := by
  let := ProjIntegral.integral G hG
  let : Algebra (Away G b) (Proj G).functionField := (ProjChartFunctionField.chartMap G hG hb0).toAlgebra
  have : IsFractionRing (Away G b) (Proj G).functionField :=
    ProjChartFunctionField.chart_isFractionRing G hG hb0 hb
  exact IsFractionRing.ringEquivOfRingEquiv (K := (Proj G).functionField) (L := L) e

theorem equiv_chartMap (z : Away G b) :
    letI := ProjIntegral.integral G hG
    equiv G hG hb hb0 e (ProjChartFunctionField.chartMap G hG hb0 z) = algebraMap R L (e z) := by
  let := ProjIntegral.integral G hG
  let : Algebra (Away G b) (Proj G).functionField := (ProjChartFunctionField.chartMap G hG hb0).toAlgebra
  have : IsFractionRing (Away G b) (Proj G).functionField :=
    ProjChartFunctionField.chart_isFractionRing G hG hb0 hb
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e z

end PaperP1.ProjAffineFieldEquiv
