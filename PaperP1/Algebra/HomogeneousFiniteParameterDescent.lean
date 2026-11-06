module

public import PaperP1.Algebra.HomogeneousKernelReduction

/-! # A genuine algebraic relation reduces a finite family of linear parameters by one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousFiniteParameterDescent

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_fewer_parameters {F A : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] {n : ℕ}
    (g : Fin (n + 1) → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hbad : ¬ Function.Injective (aeval (R := F) g)) :
    ∃ u : Fin n → A, (∀ i, u i ∈ H 1) ∧ (aeval (R := F) u).Finite := by
  let φ := aeval (R := F) g
  let I := RingHom.ker φ
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) F) :=
    GradedPolynomialPresentation.kernel_homogeneous H g hg
  have hne : I ≠ ⊥ := by
    intro hzero
    exact hbad ((RingHom.injective_iff_ker_eq_bot φ).mpr hzero)
  obtain ⟨e, p, hp, hp0, hpI⟩ := HomogeneousKernelReduction.exists_homogeneous_relation I hI hne
  obtain ⟨u, hu, hfiniteu⟩ := HomogeneousLinearNormalization.exists_parameters I p hp hp0 hpI
  have hkill (P : MvPolynomial (Fin (n + 1)) F) (hP : P ∈ I) : φ P = 0 := hP
  let ψ := Ideal.Quotient.liftₐ I φ hkill
  have hψcomp : ψ.comp (Ideal.Quotient.mkₐ F I) = φ := Ideal.Quotient.liftₐ_comp I φ hkill
  have hψ : ψ.Finite := AlgHom.Finite.of_comp_finite (by
    change (ψ.comp (Ideal.Quotient.mkₐ F I)).Finite
    rw [hψcomp]
    exact hfinite)
  let u' : Fin n → A := fun i ↦ ψ (u i)
  have hu' (i : Fin n) : u' i ∈ H 1 := by
    obtain ⟨P, hP, he⟩ := Submodule.mem_map.mp (hu i)
    dsimp [u']
    rw [← he]
    exact GradedPolynomialGenerators.eval_homogeneous H g hg 1 P hP
  have heval : aeval (R := F) u' = ψ.comp (aeval (R := F) u) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨u', hu', ?_⟩
  rw [heval]
  exact AlgHom.Finite.comp hψ hfiniteu

end PaperP1.HomogeneousFiniteParameterDescent
