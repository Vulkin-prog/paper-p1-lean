module

public import PaperP1.Algebra.GradedVeroneseGrading
public import PaperP1.Algebra.PolynomialPowerMapFinite
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Finite normalization descends to actual Veronese subalgebras via parameter powers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VeroneseFinitePowerParameters

open MvPolynomial

variable {F B σ : Type*} [Field F] [CommRing B] [Algebra F B]
  (H : ℕ → Submodule F B) [GradedAlgebra H] (g : σ → B) (hg : ∀ i, g i ∈ H 1) (D : ℕ)

local instance polynomialRing : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial σ F) :=
  (polynomialRing (F := F) (σ := σ)).toSemiring

def parameters (i : σ) : GradedVeroneseAlgebra.veronese H D :=
  ⟨g i ^ D, GradedVeroneseAlgebra.piece_mem H D 1 (by
    simpa only [smul_eq_mul, mul_one, one_mul] using SetLike.pow_mem_graded D (hg i))⟩

theorem parameter_mem (i : σ) : parameters H g hg D i ∈ GradedVeroneseGrading.piece H D 1 := by
  change g i ^ D ∈ H (1 * D)
  simpa only [smul_eq_mul, mul_one, one_mul] using SetLike.pow_mem_graded D (hg i)

def parameterMap : MvPolynomial σ F →ₐ[F] GradedVeroneseAlgebra.veronese H D :=
  aeval (parameters H g hg D)

def ambientMap : MvPolynomial σ F →ₐ[F] B := (aeval g).comp (PolynomialPowerMapFinite.map F σ D)

theorem diagram : (GradedVeroneseAlgebra.veronese H D).val.comp (parameterMap H g hg D) =
    ambientMap g D := by
  apply MvPolynomial.algHom_ext
  intro i
  change (parameterMap H g hg D (X i) : B) = aeval g (PolynomialPowerMapFinite.map F σ D (X i))
  rw [parameterMap, aeval_X]
  change g i ^ D = aeval g (aeval (fun j ↦ X j ^ D) (X i))
  rw [aeval_X, map_pow, aeval_X]

theorem diagram_apply (p : MvPolynomial σ F) :
    (parameterMap H g hg D p : B) = ambientMap g D p := DFunLike.congr_fun (diagram H g hg D) p

@[instance_reducible] def parameterAlgebra : Algebra (MvPolynomial σ F) (GradedVeroneseAlgebra.veronese H D) :=
  (parameterMap H g hg D).toRingHom.toAlgebra

@[instance_reducible] def ambientAlgebra : Algebra (MvPolynomial σ F) B :=
  (ambientMap g D).toRingHom.toAlgebra

def inclusion :
    letI := parameterAlgebra H g hg D
    letI := ambientAlgebra (F := F) g D
    GradedVeroneseAlgebra.veronese H D →ₗ[MvPolynomial σ F] B := by
  letI := parameterAlgebra H g hg D
  letI := ambientAlgebra (F := F) g D
  exact {
    toFun := Subtype.val
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun p x ↦ by
      change (parameterMap H g hg D p : B) * (x : B) = ambientMap g D p * (x : B)
      rw [diagram_apply] }

include hg in
theorem finite [Finite σ] (hD : 0 < D) (hf : (aeval (R := F) g).Finite) :
    (parameterMap H g hg D).Finite := by
  let := parameterAlgebra H g hg D
  let := ambientAlgebra (F := F) g D
  have : Module.Finite (MvPolynomial σ F) B :=
    AlgHom.Finite.comp hf (PolynomialPowerMapFinite.finite F σ D hD)
  exact Module.Finite.of_injective (inclusion H g hg D) Subtype.val_injective

end PaperP1.VeroneseFinitePowerParameters
