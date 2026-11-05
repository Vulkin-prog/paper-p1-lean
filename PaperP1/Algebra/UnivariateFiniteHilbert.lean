module

public import PaperP1.Algebra.UnivariateGradedModuleHilbert
public import PaperP1.Algebra.FiniteHomogeneousModuleGenerators
public import PaperP1.Algebra.GradedPolynomialGenerators

/-! # Finiteness over one genuine linear parameter forces an eventual constant Hilbert function -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnivariateFiniteHilbert

theorem eventually_constant {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (x : A) (hx : x ∈ H 1) (hfinite : (MvPolynomial.aeval (R := F) (fun _ : Unit ↦ x)).Finite) :
    ∃ N c : ℕ, ∀ n : ℕ, N ≤ n → Module.finrank F (H n) = c := by
  let g : Unit → A := fun _ ↦ x
  let f := GradedPolynomialGenerators.gradedEval H g (fun _ ↦ hx)
  let : Algebra (MvPolynomial Unit F) A := (MvPolynomial.aeval g).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial Unit F) A := hfinite
  obtain ⟨ι, hι, v, d, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial Unit F) H
  let : Fintype ι := hι
  exact UnivariateGradedModuleHilbert.eventually_constant H f
    (fun a ↦ (MvPolynomial.aeval (R := F) g).commutes a) v d hv
    (GradedModulePieceMap.generators_of_span f v hspan)

end PaperP1.UnivariateFiniteHilbert
