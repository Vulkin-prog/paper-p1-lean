module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # A polynomial algebra is finite over the subalgebra of positive coordinate powers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialPowerMapFinite

open MvPolynomial

variable (F σ : Type*) [CommRing F]

local instance polynomialRing : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial σ F) := (polynomialRing F σ).toSemiring

def map (D : ℕ) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F := aeval (fun i ↦ X i ^ D)

@[instance_reducible] def algebra (D : ℕ) : Algebra (MvPolynomial σ F) (MvPolynomial σ F) :=
  (map F σ D).toRingHom.toAlgebra

theorem map_C (D : ℕ) (a : F) : map F σ D (C a) = C a := (map F σ D).commutes a

theorem variable_integral (D : ℕ) (hD : 0 < D) (i : σ) :
    letI := algebra F σ D
    IsIntegral (MvPolynomial σ F) (X i : MvPolynomial σ F) := by
  let := algebra F σ D
  apply IsIntegral.of_pow hD
  have he : algebraMap (MvPolynomial σ F) (MvPolynomial σ F) (X i) = X i ^ D := aeval_X _ i
  rw [← he]
  exact isIntegral_algebraMap

theorem generated (D : ℕ) :
    letI := algebra F σ D
    Algebra.adjoin (MvPolynomial σ F) (Set.range (X : σ → MvPolynomial σ F)) = ⊤ := by
  let := algebra F σ D
  apply top_unique
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : algebraMap (MvPolynomial σ F) (MvPolynomial σ F) (C a) = C a := map_C F σ D a
    rw [← he]
    exact (Algebra.adjoin (MvPolynomial σ F) (Set.range (X : σ → MvPolynomial σ F))).algebraMap_mem _
  | add p q hp hq => exact Subalgebra.add_mem _ (hp (by trivial)) (hq (by trivial))
  | mul_X p i hp => exact Subalgebra.mul_mem _ (hp (by trivial)) (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem finite [Finite σ] (D : ℕ) (hD : 0 < D) : (map F σ D).Finite := by
  let := algebra F σ D
  let : Module (MvPolynomial σ F) (MvPolynomial σ F) := Algebra.toModule
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral
    (R := MvPolynomial σ F) (Set.finite_range (X : σ → MvPolynomial σ F))
    (fun _ ⟨i, hi⟩ ↦ hi ▸ variable_integral F σ D hD i)
  change Module.Finite (MvPolynomial σ F) (MvPolynomial σ F)
  exact Module.Finite.of_surjective
    (Algebra.adjoin (MvPolynomial σ F) (Set.range (X : σ → MvPolynomial σ F))).val.toLinearMap (by
      intro p
      exact ⟨⟨p, by rw [generated F σ D]; trivial⟩, rfl⟩)

end PaperP1.PolynomialPowerMapFinite
