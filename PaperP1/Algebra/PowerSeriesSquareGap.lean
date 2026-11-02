module

public import PaperP1.Algebra.SquareInFractionField
public import Mathlib.RingTheory.PowerSeries.Inverse

/-! # A simple power-series zero remains nonsquare in the actual fraction field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PowerSeriesSquareGap

theorem not_square {K : Type*} [Field K] (u : PowerSeries K) (hu : IsUnit u) :
    ¬ IsSquare ((PowerSeries.X : PowerSeries K) * u) :=
  ((irreducible_mul_isUnit hu).mpr PowerSeries.irreducible_X).not_isSquare

theorem not_fraction_square {K : Type*} [Field K] (u : PowerSeries K) (hu : IsUnit u) :
    ¬ IsSquare (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.X * u)) := by
  rw [SquareInFractionField.square_reflect]
  exact not_square u hu

end PaperP1.PowerSeriesSquareGap
