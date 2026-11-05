module

public import PaperP1.Algebra.HomogeneousLinearNormalization
public import PaperP1.Algebra.GradedPolynomialPresentation
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # A noninjective finite two-parameter evaluation reduces to one genuine linear parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousKernelReduction

open MvPolynomial DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_homogeneous_relation {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) (hne : I ≠ ⊥) :
    ∃ (e : ℕ) (p : MvPolynomial σ F), p.IsHomogeneous e ∧ p ≠ 0 ∧ p ∈ I := by
  classical
  obtain ⟨p, hpI, hp0⟩ := I.ne_bot_iff.mp hne
  obtain ⟨e, he⟩ : ∃ e : ℕ, (decompose (homogeneousSubmodule σ F) p e : MvPolynomial σ F) ≠ 0 := by
    by_contra! hh
    apply hp0
    rw [← sum_support_decompose (homogeneousSubmodule σ F) p]
    exact Finset.sum_eq_zero (fun e _he ↦ hh e)
  exact ⟨e, decompose (homogeneousSubmodule σ F) p e,
    (decompose (homogeneousSubmodule σ F) p e).property, he, (hI.mem_iff.mp hpI) e⟩

theorem exists_one_parameter {F A : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hbad : ¬ Function.Injective (aeval (R := F) g)) :
    ∃ x : A, x ∈ H 1 ∧ (aeval (R := F) (fun _ : Unit ↦ x)).Finite := by
  classical
  let φ := aeval (R := F) g
  let I := RingHom.ker φ
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin 2) F) :=
    GradedPolynomialPresentation.kernel_homogeneous H g hg
  have hne : I ≠ ⊥ := by
    intro hzero
    exact hbad ((RingHom.injective_iff_ker_eq_bot φ).mpr hzero)
  obtain ⟨e, p, hp, hp0, hpI⟩ := exists_homogeneous_relation I hI hne
  obtain ⟨k, hk, hfinitek⟩ := HomogeneousLinearNormalization.exists_parameters I p hp hp0 hpI
  have hkill (P : MvPolynomial (Fin 2) F) (hP : P ∈ I) : φ P = 0 := hP
  let ψ := Ideal.Quotient.liftₐ I φ hkill
  have hψcomp : ψ.comp (Ideal.Quotient.mkₐ F I) = φ := Ideal.Quotient.liftₐ_comp I φ hkill
  have hψ : ψ.Finite := AlgHom.Finite.of_comp_finite (by
    change (ψ.comp (Ideal.Quotient.mkₐ F I)).Finite
    rw [hψcomp]
    exact hfinite)
  let k' : Fin 1 → A := fun i ↦ ψ (k i)
  have hk' (i : Fin 1) : k' i ∈ H 1 := by
    obtain ⟨P, hP, he⟩ := Submodule.mem_map.mp (hk i)
    dsimp [k']
    rw [← he]
    exact GradedPolynomialGenerators.eval_homogeneous H g hg 1 P hP
  have heval : aeval (R := F) k' = ψ.comp (aeval (R := F) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hfinitek' : (aeval (R := F) k').Finite := by
    rw [heval]
    exact AlgHom.Finite.comp hψ hfinitek
  let ρ : MvPolynomial Unit F →ₐ[F] MvPolynomial (Fin 1) F := rename (fun _ ↦ 0)
  have hρ : ρ.Finite := AlgHom.Finite.of_surjective _ (MvPolynomial.rename_surjective _ (by
    intro i
    exact ⟨(), Subsingleton.elim _ _⟩))
  have heunit : aeval (R := F) (fun _ : Unit ↦ k' 0) = (aeval (R := F) k').comp ρ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, ρ, rename_X]
  refine ⟨k' 0, hk' 0, ?_⟩
  rw [heunit]
  exact AlgHom.Finite.comp hfinitek' hρ

end PaperP1.HomogeneousKernelReduction
