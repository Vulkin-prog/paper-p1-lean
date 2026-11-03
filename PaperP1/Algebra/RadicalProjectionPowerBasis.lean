module

public import PaperP1.Algebra.RadicalProjectionPolynomial
public import Mathlib.RingTheory.AdjoinRoot

/-! # The actual affine image is free over the base with its literal power basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RadicalProjectionPowerBasis

open Module Polynomial PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.RadicalProjectionPolynomial

def imagePowerBasis (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    PowerBasis R (imageAlgebra R s) :=
  (AdjoinRoot.powerBasis' (equation_monic R s)).map (quotientEquivImage R K s hs)

theorem imagePowerBasis_dim (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    (imagePowerBasis R K s hs).dim = 2 ^ s.length := equation_degree R K s hs

theorem imagePowerBasis_gen (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    ((imagePowerBasis R K s hs).gen : Tower R s) = radicalSum R s := by
  change (quotientEquivImage R K s hs (Ideal.Quotient.mk _ X) : Tower R s) = radicalSum R s
  rw [quotientEquivImage_apply, aeval_X]

theorem imagePowerBasis_apply (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K)))
    (i : Fin (imagePowerBasis R K s hs).dim) :
    ((imagePowerBasis R K s hs).basis i : Tower R s) = radicalSum R s ^ (i : ℕ) := by
  rw [PowerBasis.basis_eq_pow]
  change (imagePowerBasis R K s hs).gen.val ^ (i : ℕ) = _
  rw [imagePowerBasis_gen]

theorem image_free (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) : Module.Free R (imageAlgebra R s) :=
  .of_basis (imagePowerBasis R K s hs).basis

theorem image_finite (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) : Module.Finite R (imageAlgebra R s) :=
  .of_basis (imagePowerBasis R K s hs).basis

theorem image_finrank (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) : finrank R (imageAlgebra R s) = 2 ^ s.length :=
  (imagePowerBasis R K s hs).finrank.trans (imagePowerBasis_dim R K s hs)

end PaperP1.RadicalProjectionPowerBasis
