module

public import PaperP1.Algebra.TwoVariableGradedHilbert

/-! # Finite degree-one parameters pass through actual graded equivalences and finite maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGradedParameters

open MvPolynomial

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

local instance polynomialRing : CommRing (MvPolynomial (Fin 2) F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial (Fin 2) F) := (polynomialRing (F := F)).toSemiring

def HasParameters (G : ℕ → Submodule F A) : Prop :=
  ∃ g : Fin 2 → A, (∀ i, g i ∈ G 1) ∧ (aeval (R := F) g).Finite

theorem of_equiv (G : ℕ → Submodule F A) (H : ℕ → Submodule F B) (e : A ≃ₐ[F] B)
    (he : (G 1).map e.toLinearMap = H 1) (hp : HasParameters H) : HasParameters G := by
  obtain ⟨g, hg, hf⟩ := hp
  let g' (i : Fin 2) : A := e.symm (g i)
  refine ⟨g', fun i ↦ ?_, ?_⟩
  · have hm : g i ∈ (G 1).map e.toLinearMap := he ▸ hg i
    obtain ⟨a, ha, hga⟩ := Submodule.mem_map.mp hm
    have ht : g' i = a := by change e.symm (g i) = a; rw [← hga]; exact e.symm_apply_apply a
    exact ht ▸ ha
  · have heval : aeval (R := F) g' = e.symm.toAlgHom.comp (aeval (R := F) g) := by
      apply MvPolynomial.algHom_ext
      intro i
      change aeval g' (X i) = e.symm (aeval g (X i))
      rw [aeval_X, aeval_X]
    rw [heval]
    exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective e.symm.toAlgHom e.symm.surjective) hf

theorem of_finite_map (G : ℕ → Submodule F A) (H : ℕ → Submodule F B) (f : A →ₐ[F] B)
    (hh : ∀ a : A, a ∈ G 1 → f a ∈ H 1) (hf : f.Finite) (hp : HasParameters G) : HasParameters H := by
  obtain ⟨g, hg, hfinite⟩ := hp
  let g' (i : Fin 2) : B := f (g i)
  refine ⟨g', fun i ↦ hh (g i) (hg i), ?_⟩
  have heval : aeval (R := F) g' = f.comp (aeval (R := F) g) := by
    apply MvPolynomial.algHom_ext
    intro i
    change aeval g' (X i) = f (aeval g (X i))
    rw [aeval_X, aeval_X]
  rw [heval]
  exact AlgHom.Finite.comp hf hfinite

theorem exists_polynomial [IsDomain B] (H : ℕ → Submodule F B) [GradedAlgebra H]
    [∀ n, Module.Finite F (H n)] (hp : HasParameters H) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p := by
  obtain ⟨g, hg, hf⟩ := hp
  exact TwoVariableGradedHilbert.exists_polynomial_of_finite H g hg hf

end PaperP1.FiniteGradedParameters
