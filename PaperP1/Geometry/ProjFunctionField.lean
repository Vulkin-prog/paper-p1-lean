module

public import PaperP1.Geometry.ProjIntegral
public import Mathlib.Algebra.Field.Equiv

/-! # The actual scheme function field of Proj is its degree-zero homogeneous fraction field -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjFunctionField

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

variable {A σ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G]

abbrev degreeZeroField := AtPrime G (⊥ : Ideal A)

def equiv (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    letI := ProjIntegral.integral G hpos
    (Proj G).functionField ≃+* degreeZeroField G := by
  let := ProjIntegral.integral G hpos
  let e : (Proj G).functionField ≅ CommRingCat.of (degreeZeroField G) := by
    change (Proj G).presheaf.stalk (genericPoint (Proj G)) ≅ CommRingCat.of (AtPrime G (⊥ : Ideal A))
    rw [ProjIntegral.genericPoint_eq_zero G hpos]
    exact AlgebraicGeometry.Proj.stalkIso G (ProjIntegral.zeroPoint G hpos)
  exact e.commRingCatIsoToRingEquiv

theorem degreeZero_isField (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    IsField (degreeZeroField G) := by
  let := ProjIntegral.integral G hpos
  exact MulEquiv.isField (Field.toIsField (Proj G).functionField) (equiv G hpos).symm.toMulEquiv

omit [AddSubgroupClass σ A] [GradedRing G] in
theorem fraction_representation (x : degreeZeroField G) :
    ∃ (n : ℕ) (a b : G n), ∃ hb : (b : A) ≠ 0,
      HomogeneousLocalization.mk ⟨n, a, b, hb⟩ = x := by
  obtain ⟨⟨n, a, b, hb⟩, rfl⟩ := HomogeneousLocalization.mk_surjective x
  exact ⟨n, a, b, hb, rfl⟩

end PaperP1.ProjFunctionField
