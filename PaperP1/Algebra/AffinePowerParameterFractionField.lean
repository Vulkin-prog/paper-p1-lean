module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.Localization.FractionRing
public import PaperP1.Algebra.CoordinateFractionFieldGenerators
public import PaperP1.Algebra.TwoPowerFieldDimension

/-! # The actual ordered affine power parameters give a finite function-field extension of dimension at most D squared

The parameter variables map to Y^D and X^D in that order. The fraction
map, power equations, exhaustive generators and dimension bound are all
constructed over an arbitrary coefficient field.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.AffinePowerParameterFractionField
open Polynomial
variable (F : Type*) [Field F]
abbrev Parameters := MvPolynomial (Fin 2) F
abbrev Base := F[X][X]
abbrev ParameterField := FractionRing (Parameters F)
abbrev AmbientField := FractionRing (Base F)

def chart : Parameters F ≃ₐ[F] Base F :=
  (MvPolynomial.renameEquiv F (Equiv.swap (0 : Fin 2) 1)).trans (Bivariate.equivMvPolynomial F).symm

theorem chart_zero : chart F (MvPolynomial.X 0) = (X : Base F) := by
  simp [chart, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

theorem chart_one : chart F (MvPolynomial.X 1) = C X := by
  simp [chart, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]

def powerMap (D : ℕ) : Parameters F →ₐ[F] Base F :=
  (chart F).toAlgHom.comp (MvPolynomial.expand D)

theorem powerMap_injective (D : ℕ) (hD : 0 < D) : Function.Injective (powerMap F D) :=
  (chart F).injective.comp (MvPolynomial.expand_injective hD)

theorem powerMap_zero (D : ℕ) : powerMap F D (MvPolynomial.X 0) = (X : Base F) ^ D := by
  change chart F (MvPolynomial.expand D (MvPolynomial.X 0)) = _
  rw [MvPolynomial.expand_X, map_pow, chart_zero]

theorem powerMap_one (D : ℕ) : powerMap F D (MvPolynomial.X 1) = (C X : Base F) ^ D := by
  change chart F (MvPolynomial.expand D (MvPolynomial.X 1)) = _
  rw [MvPolynomial.expand_X, map_pow, chart_one]

def polynomialMap (D : ℕ) : Parameters F →ₐ[F] AmbientField F :=
  (IsScalarTower.toAlgHom F (Base F) (AmbientField F)).comp (powerMap F D)

theorem polynomialMap_injective (D : ℕ) (hD : 0 < D) : Function.Injective (polynomialMap F D) :=
  (IsFractionRing.injective (Base F) (AmbientField F)).comp (powerMap_injective F D hD)

def fractionMap (D : ℕ) (hD : 0 < D) : ParameterField F →ₐ[F] AmbientField F :=
  IsFractionRing.liftAlgHom (polynomialMap_injective F D hD)

@[instance_reducible]
def fractionAlgebra (D : ℕ) (hD : 0 < D) : Algebra (ParameterField F) (AmbientField F) :=
  (fractionMap F D hD).toRingHom.toAlgebra

section Local
variable (D : ℕ) (hD : 0 < D)

theorem fractionMap_base (P : Parameters F) :
    letI := fractionAlgebra F D hD
    algebraMap (ParameterField F) (AmbientField F) (algebraMap (Parameters F) (ParameterField F) P) =
      algebraMap (Base F) (AmbientField F) (powerMap F D P) := by
  let := fractionAlgebra F D hD
  change IsFractionRing.lift (polynomialMap_injective F D hD) (algebraMap (Parameters F) (ParameterField F) P) = _
  exact IsFractionRing.lift_algebraMap (polynomialMap_injective F D hD) P

theorem power_zero : letI := fractionAlgebra F D hD
    (algebraMap (Base F) (AmbientField F) X) ^ D =
    algebraMap (ParameterField F) (AmbientField F) (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 0)) := by
  let := fractionAlgebra F D hD
  rw [fractionMap_base, powerMap_zero, map_pow]

theorem power_one : letI := fractionAlgebra F D hD
    (algebraMap (Base F) (AmbientField F) (C X)) ^ D =
    algebraMap (ParameterField F) (AmbientField F) (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 1)) := by
  let := fractionAlgebra F D hD
  rw [fractionMap_base, powerMap_one, map_pow]

theorem base_generated : Algebra.adjoin F (Set.range (![X, C X] : Fin 2 → Base F)) = ⊤ := by
  have hcoords : (fun i : Fin 2 ↦ chart F (MvPolynomial.X i)) = ![X, C X] := by
    funext i
    fin_cases i
    · exact chart_zero F
    · exact chart_one F
  have hh := AlgHom.map_adjoin (chart F).toAlgHom (Set.range (MvPolynomial.X : Fin 2 → Parameters F))
  rw [MvPolynomial.adjoin_range_X, Algebra.map_top] at hh
  have him : (chart F).toAlgHom '' Set.range (MvPolynomial.X : Fin 2 → Parameters F) =
      Set.range (![X, C X] : Fin 2 → Base F) := by
    rw [← Set.range_comp]
    exact congrArg Set.range hcoords
  rw [him] at hh
  exact hh.symm.trans ((AlgHom.range_eq_top (chart F).toAlgHom).mpr (chart F).surjective)

theorem generators : letI := fractionAlgebra F D hD
    IntermediateField.adjoin (ParameterField F) ({algebraMap (Base F) (AmbientField F) X,
      algebraMap (Base F) (AmbientField F) (C X)} : Set (AmbientField F)) = ⊤ := by
  let := fractionAlgebra F D hD
  let : IsScalarTower F (ParameterField F) (AmbientField F) := IsScalarTower.of_algHom (fractionMap F D hD)
  have hh := PaperP1.CoordinateFractionFieldGenerators.fraction_field_generated
    (F := F) (K := ParameterField F) (L := AmbientField F) (![X, C X] : Fin 2 → Base F) (base_generated F)
  have hcoords : (fun i : Fin 2 ↦ algebraMap (Base F) (AmbientField F) (![X, C X] i)) =
      ![algebraMap (Base F) (AmbientField F) X, algebraMap (Base F) (AmbientField F) (C X)] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hcoords, Matrix.range_cons_cons_empty] using hh

theorem finiteDimensional : letI := fractionAlgebra F D hD
    FiniteDimensional (ParameterField F) (AmbientField F) := by
  let := fractionAlgebra F D hD
  exact PaperP1.TwoPowerFieldDimension.finiteDimensional _ _ D hD
    (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 0))
    (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 1))
    (power_zero F D hD) (power_one F D hD) (generators F D hD)

theorem dimension_le : letI := fractionAlgebra F D hD
    Module.finrank (ParameterField F) (AmbientField F) ≤ D ^ 2 := by
  let := fractionAlgebra F D hD
  exact PaperP1.TwoPowerFieldDimension.dimension_le _ _ D hD
    (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 0))
    (algebraMap (Parameters F) (ParameterField F) (MvPolynomial.X 1))
    (power_zero F D hD) (power_one F D hD) (generators F D hD)

end Local
end PaperP1.AffinePowerParameterFractionField
