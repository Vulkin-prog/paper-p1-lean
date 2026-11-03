module

public import PaperP1.Geometry.ProjFunctionFieldCompatibility

/-! # The actual scheme function field is the fraction field of a nonzero degree-one chart -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjChartFunctionField

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

variable {A σ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G]
  (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) {b : A} (hb0 : b ≠ 0)

include hpos hb0 in
theorem nonempty_basicOpen : Nonempty (Proj.basicOpen G b) := by
  refine ⟨⟨ProjIntegral.zeroPoint G hpos, ?_⟩⟩
  change b ≠ 0
  exact hb0

def chartMapCat :
    letI := ProjIntegral.integral G hpos
    CommRingCat.of (Away G b) ⟶ (Proj G).functionField := by
  let := ProjIntegral.integral G hpos
  have : Nonempty (Proj.basicOpen G b) := nonempty_basicOpen G hpos hb0
  exact Proj.awayToSection G b ≫ (Proj G).germToFunctionField (Proj.basicOpen G b)

def chartMap :
    letI := ProjIntegral.integral G hpos
    Away G b →+* (Proj G).functionField := by
  let := ProjIntegral.integral G hpos
  exact (chartMapCat G hpos hb0).hom

theorem chart_isFractionRing (hb : b ∈ G 1) :
    letI := ProjIntegral.integral G hpos
    letI : Algebra (Away G b) (Proj G).functionField := (chartMap G hpos hb0).toAlgebra
    IsFractionRing (Away G b) (Proj G).functionField := by
  let := ProjIntegral.integral G hpos
  have : Nonempty (Proj.basicOpen G b) := nonempty_basicOpen G hpos hb0
  have : IsFractionRing Γ(Proj G, Proj.basicOpen G b) (Proj G).functionField :=
    functionField_isFractionRing_of_isAffineOpen (Proj G) (Proj.basicOpen G b)
      (Proj.isAffineOpen_basicOpen G b hb (by decide : 0 < 1))
  let e : Γ(Proj G, Proj.basicOpen G b) ≃+* Away G b :=
    (Proj.basicOpenIsoAway G b hb (by decide : 0 < 1)).symm.commRingCatIsoToRingEquiv
  have hs := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (Proj G).functionField e).mp
    (inferInstance : IsFractionRing Γ(Proj G, Proj.basicOpen G b) (Proj G).functionField)
  exact hs

end PaperP1.ProjChartFunctionField
