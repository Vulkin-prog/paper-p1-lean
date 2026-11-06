module

public import PaperP1.Algebra.AffinePowerParameterFractionField
public import PaperP1.Algebra.QuadraticTowerBaseChange
public import PaperP1.Algebra.PolynomialPowerMapFinite
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # The actual affine quadratic source injects into its finite generic algebra of dimension at most 2^k D squared

No domain, branch independence or nonzero radical coefficient is assumed.
The exact source parameter map commutes with the generic fraction map.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LocalizedAffineQuadraticSource
open Polynomial PaperP1.FiniteQuadraticTower PaperP1.AffinePowerParameterFractionField
variable (F : Type*) [Field F]
abbrev Source (s : List (Base F)) := Tower (Base F) s
abbrev Generic (s : List (Base F)) := Tower (AmbientField F) (s.map (algebraMap (Base F) (AmbientField F)))

def injection (s : List (Base F)) : Source F s →+* Generic F s :=
  (PaperP1.QuadraticTowerBaseChange.mapData (algebraMap (Base F) (AmbientField F)) s).hom

theorem injection_injective (s : List (Base F)) : Function.Injective (injection F s) :=
  PaperP1.QuadraticTowerBaseChange.map_injective _ (IsFractionRing.injective (Base F) (AmbientField F)) s

theorem injection_base (s : List (Base F)) (P : Base F) :
    injection F s (algebraMap (Base F) (Source F s) P) =
      algebraMap (AmbientField F) (Generic F s) (algebraMap (Base F) (AmbientField F) P) :=
  (PaperP1.QuadraticTowerBaseChange.mapData (algebraMap (Base F) (AmbientField F)) s).commutes P

@[instance_reducible]
def sourceAlgebra (D : ℕ) (s : List (Base F)) : Algebra (Parameters F) (Source F s) :=
  Algebra.compHom (Source F s) (powerMap F D).toRingHom

theorem source_finite (D : ℕ) (hD : 0 < D) (s : List (Base F)) :
    letI := sourceAlgebra F D s
    Module.Finite (Parameters F) (Source F s) := by
  let : Algebra (Parameters F) (Base F) := (powerMap F D).toRingHom.toAlgebra
  let := sourceAlgebra F D s
  let : IsScalarTower (Parameters F) (Base F) (Source F s) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : Module.Finite (Parameters F) (Base F) :=
    (AlgHom.Finite.of_surjective (chart F).toAlgHom (chart F).surjective).comp
      (PaperP1.PolynomialPowerMapFinite.finite F (Fin 2) D hD)
  exact Module.Finite.trans (Base F) (Source F s)

@[instance_reducible]
def genericAlgebra (D : ℕ) (hD : 0 < D) (s : List (Base F)) : Algebra (ParameterField F) (Generic F s) :=
  Algebra.compHom (Generic F s) (fractionMap F D hD).toRingHom

theorem genericTower (D : ℕ) (hD : 0 < D) (s : List (Base F)) :
    letI := fractionAlgebra F D hD
    letI := genericAlgebra F D hD s
    IsScalarTower (ParameterField F) (AmbientField F) (Generic F s) := by
  let := fractionAlgebra F D hD
  let := genericAlgebra F D hD s
  exact IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

theorem generic_finite (D : ℕ) (hD : 0 < D) (s : List (Base F)) :
    letI := genericAlgebra F D hD s
    Module.Finite (ParameterField F) (Generic F s) := by
  let := fractionAlgebra F D hD
  let := genericAlgebra F D hD s
  let : IsScalarTower (ParameterField F) (AmbientField F) (Generic F s) := genericTower F D hD s
  let : Module.Finite (ParameterField F) (AmbientField F) := finiteDimensional F D hD
  exact Module.Finite.trans (AmbientField F) (Generic F s)

theorem generic_dimension (D : ℕ) (hD : 0 < D) (s : List (Base F)) :
    letI := genericAlgebra F D hD s
    Module.finrank (ParameterField F) (Generic F s) ≤ 2 ^ s.length * D ^ 2 := by
  let := fractionAlgebra F D hD
  let := genericAlgebra F D hD s
  let : IsScalarTower (ParameterField F) (AmbientField F) (Generic F s) := genericTower F D hD s
  rw [← Module.finrank_mul_finrank (ParameterField F) (AmbientField F) (Generic F s),
    PaperP1.FiniteQuadraticTower.finrank, List.length_map]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ s.length) (dimension_le F D hD)

theorem generic_nontrivial (s : List (Base F)) : Nontrivial (Generic F s) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he : algebraMap (AmbientField F) (Generic F s) 0 =
      algebraMap (AmbientField F) (Generic F s) 1 := by simpa only [map_zero, map_one] using h
  exact zero_ne_one (PaperP1.FiniteQuadraticTower.base_injective _ _ he)

theorem parameter_compatibility (D : ℕ) (hD : 0 < D) (s : List (Base F)) (P : Parameters F) :
    letI := sourceAlgebra F D s
    letI := genericAlgebra F D hD s
    injection F s (algebraMap (Parameters F) (Source F s) P) =
      algebraMap (ParameterField F) (Generic F s) (algebraMap (Parameters F) (ParameterField F) P) := by
  let := sourceAlgebra F D s
  let := genericAlgebra F D hD s
  change injection F s (algebraMap (Base F) (Source F s) (powerMap F D P)) =
    algebraMap (AmbientField F) (Generic F s) ((fractionMap F D hD) (algebraMap (Parameters F) (ParameterField F) P))
  rw [injection_base]
  exact congrArg (algebraMap (AmbientField F) (Generic F s)) (fractionMap_base F D hD P).symm

end PaperP1.LocalizedAffineQuadraticSource
