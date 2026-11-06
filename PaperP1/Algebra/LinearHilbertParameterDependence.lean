module

public import PaperP1.Algebra.TernaryPolynomialHilbert
public import PaperP1.Algebra.GradedInjectiveHilbertComparison
public import PaperP1.Algebra.GradedPolynomialGenerators
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Linear actual Hilbert growth forbids three algebraically independent degree-one coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHilbertParameterDependence

open Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem three_not_injective {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (C a * X + C b))
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) : ¬ Function.Injective (MvPolynomial.aeval (R := F) g) := by
  intro hinj
  have hh := GradedInjectiveHilbertComparison.coefficient_le
    (GradedPolynomialGenerators.gradedEval H g hg)
    (fun r ↦ (MvPolynomial.aeval (R := F) g).commutes r) hinj
    TernaryPolynomialHilbert.polynomial (C a * X + C b) 2 TernaryPolynomialHilbert.natDegree_le
    (by
      compute_degree
      norm_num) (TernaryPolynomialHilbert.isHilbertPolynomial F) hp
  rw [TernaryPolynomialHilbert.coeff_two] at hh
  norm_num at hh

theorem not_injective_of_three_le {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (C a * X + C b))
    (n : ℕ) (hn : 3 ≤ n) (g : Fin n → A) (hg : ∀ i, g i ∈ H 1) :
    ¬ Function.Injective (MvPolynomial.aeval (R := F) g) := by
  intro hinj
  let e : Fin 3 → Fin n := Fin.castLE hn
  let g' : Fin 3 → A := fun i ↦ g (e i)
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) hij)
  have heval : MvPolynomial.aeval (R := F) g' =
      (MvPolynomial.aeval (R := F) g).comp (MvPolynomial.rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    rfl
  apply three_not_injective H a b hp g' (fun i ↦ hg (e i))
  rw [heval]
  exact hinj.comp (MvPolynomial.rename_injective e he)

end PaperP1.LinearHilbertParameterDependence
