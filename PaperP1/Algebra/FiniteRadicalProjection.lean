module

public import PaperP1.Algebra.FiniteQuadraticTower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-! # The actual sum-of-radicals projection is finite -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRadicalProjection

open PaperP1.FiniteQuadraticTower

def radicalSum (R : Type*) [CommRing R] (s : List R) : Tower R s := ∑ i : Fin s.length, root R s i

def imageAlgebra (R : Type*) [CommRing R] (s : List R) : Subalgebra R (Tower R s) :=
  Algebra.adjoin R {radicalSum R s}

theorem image_eq_range (R : Type*) [CommRing R] (s : List R) :
    imageAlgebra R s = (Polynomial.aeval (radicalSum R s)).range :=
  Algebra.adjoin_singleton_eq_range_aeval R (radicalSum R s)

theorem finite_over_image (R : Type*) [CommRing R] (s : List R) :
    Module.Finite (imageAlgebra R s) (Tower R s) :=
  Module.Finite.of_restrictScalars_finite R (imageAlgebra R s) (Tower R s)

theorem sum_integral (R : Type*) [CommRing R] (s : List R) : IsIntegral R (radicalSum R s) :=
  IsIntegral.of_finite R _

end PaperP1.FiniteRadicalProjection
