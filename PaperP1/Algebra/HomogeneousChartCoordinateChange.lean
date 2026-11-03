module

public import PaperP1.Algebra.GradedDehomogenization

/-! # Replacing a homogeneous chart coordinate by an equal element preserves its literal map -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousChartCoordinateChange

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {b c : A}

def equiv (h : b = c) : Away G b ≃+* Away G c := by
  subst c
  exact RingEquiv.refl _

theorem equiv_dehomogenization (h : b = c) (hb : b ∈ G 1) (hc : c ∈ G 1) (a : A) :
    equiv G h (GradedDehomogenization.map G hb a) = GradedDehomogenization.map G hc a := by
  subst c
  rfl

end PaperP1.HomogeneousChartCoordinateChange
