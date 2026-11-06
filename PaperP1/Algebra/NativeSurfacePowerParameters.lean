module

public import PaperP1.Algebra.StandardVeroneseCoordinates
public import PaperP1.Algebra.VeroneseFinitePowerParameters
public import Mathlib.Algebra.MvPolynomial.Expand

/-! # The three literal coordinate powers give a finite injective standard-Veronese normalization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativeSurfacePowerParameters

open MvPolynomial StandardBaseVeronese StandardVeroneseCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable (F : Type*) [Field F] (D : ℕ)

local instance polynomialRing : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial (Fin 3) F) :=
  (polynomialRing F).toSemiring

def map : MvPolynomial (Fin 3) F →ₐ[F] nativeVeronese F D :=
  aeval (coordinatePower F D)

theorem map_X (j : Fin 3) : map F D (X j) = coordinatePower F D j := aeval_X _ j

theorem ambient_map : (nativeVeronese F D).val.comp (map F D) = expand D := by
  apply MvPolynomial.algHom_ext
  intro j
  change (map F D (X j) : MvPolynomial (Fin 3) F) = expand D (X j)
  rw [map_X, coordinatePower_val, expand_X]

theorem injective (hD : 0 < D) : Function.Injective (map F D) := by
  intro p q hpq
  apply expand_injective hD
  have he := congrArg (fun x : nativeVeronese F D ↦ (x : MvPolynomial (Fin 3) F)) hpq
  change ((nativeVeronese F D).val.comp (map F D)) p =
    ((nativeVeronese F D).val.comp (map F D)) q at he
  rwa [ambient_map] at he

theorem finite (hD : 0 < D) : (map F D).Finite := by
  have hf : (aeval (R := F) (X : Fin 3 → MvPolynomial (Fin 3) F)).Finite := by
    apply RingHom.Finite.of_surjective
    intro p
    exact ⟨p, by simp⟩
  exact VeroneseFinitePowerParameters.finite (homogeneousSubmodule (Fin 3) F)
    (X : Fin 3 → MvPolynomial (Fin 3) F) (isHomogeneous_X F) D hD hf

end PaperP1.NativeSurfacePowerParameters
