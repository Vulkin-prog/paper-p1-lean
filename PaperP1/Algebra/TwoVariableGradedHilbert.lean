module

public import PaperP1.Algebra.TwoParameterQuotientGenerators
public import PaperP1.Algebra.UnivariateGradedModuleHilbert
public import PaperP1.Algebra.GradedHilbertHyperplane
public import PaperP1.Algebra.FiniteHomogeneousModuleGenerators

/-! # Hilbert-polynomial existence for a graded domain finite over two linear parameters

This proves existence from actual finite module generation and the dimensions
of actual homogeneous submodules. It does not assume a Hilbert polynomial.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoVariableGradedHilbert

open Finset

variable {F B ι : Type*} [Field F] [CommRing B] [Algebra F B] [IsDomain B]
  (H : ℕ → Submodule F B) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
  (g : Fin 2 → B) (hg : ∀ i, g i ∈ H 1)

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

include hg in
theorem exists_polynomial_of_generators [Fintype ι]
    (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial (Fin 2) F,
      ∑ i, MvPolynomial.aeval g (a i) * v i = b) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p := by
  let := TwoParameterQuotientGenerators.grading H g hg
  let (n : ℕ) : Module.Finite F (TwoParameterQuotientGenerators.piece H g n) :=
    TwoParameterQuotientGenerators.piece_finite H g n
  have hc := UnivariateGradedModuleHilbert.eventually_constant
    (TwoParameterQuotientGenerators.piece H g)
    (TwoParameterQuotientGenerators.gradedOne H g hg)
    (TwoParameterQuotientGenerators.gradedOne_commutes H g hg)
    (fun i ↦ TwoParameterQuotientGenerators.quotientMap (F := F) g (v i)) w
    (TwoParameterQuotientGenerators.generator_mem H g v w hv)
    (TwoParameterQuotientGenerators.generators H g hg v hgen)
  by_cases hz : g 0 = 0
  · obtain ⟨M, c, hM⟩ := hc
    refine ⟨Polynomial.C (c : ℚ), M, fun n hn ↦ ?_⟩
    rw [Polynomial.eval_C, ← TwoParameterQuotientGenerators.piece_finrank_of_zero H g hz n, hM n hn]
  · exact GradedHilbertHyperplane.exists_polynomial H (hg 0) hz hc

/-- The actual polynomial evaluation defines the scalar action used below. -/
@[instance_reducible] def parameterAlgebra : Algebra (MvPolynomial (Fin 2) F) B :=
  (MvPolynomial.aeval g).toRingHom.toAlgebra

include hg in
theorem exists_polynomial_of_finite
    (hfinite : letI := parameterAlgebra (F := F) g; Module.Finite (MvPolynomial (Fin 2) F) B) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p := by
  classical
  let := parameterAlgebra (F := F) g
  let := hfinite
  obtain ⟨ι, hι, v, w, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial (Fin 2) F) H
  let := hι
  apply exists_polynomial_of_generators H g hg v w hv
  intro b
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin 2) F)).mp
    (show b ∈ Submodule.span (MvPolynomial (Fin 2) F) (Set.range v) by rw [hspan]; trivial)
  exact ⟨a, ha⟩

end PaperP1.TwoVariableGradedHilbert
