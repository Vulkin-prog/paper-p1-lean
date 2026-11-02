module

public import PaperP1.Algebra.SparseKernelBasis
public import PaperP1.Algebra.LinearCombinationSupport

/-! # A finite coordinate cut preserves a basis with controlled physical support -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SparseConstraintBasis

open Finset

universe u v w z
variable {K : Type u} {E : Type v} {J : Type w} {A : Type z}
  [DivisionRing K] [AddCommGroup E] [Module K E]

def coordinateKernelEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis J K E) (f : E →ₗ[K] V) :
    LinearMap.ker (f.comp b.repr.symm.toLinearMap) ≃ₗ[K] LinearMap.ker f :=
  b.repr.symm.ofSubmodule' (LinearMap.ker f)

theorem coordinateKernelEquiv_apply {V : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis J K E) (f : E →ₗ[K] V)
    (x : LinearMap.ker (f.comp b.repr.symm.toLinearMap)) :
    (coordinateKernelEquiv b f x).val = b.repr.symm x.val := rfl

theorem physical_combination (b : Module.Basis J K E) (g : E →ₗ[K] (A →₀ K)) (c : J →₀ K) :
    g (b.repr.symm c) = Finsupp.linearCombination K (fun j ↦ g (b j)) c := by
  rw [b.repr_symm_apply]
  have he : (g ∘ b) = (fun j ↦ g (b j)) := rfl
  have hm := Finsupp.apply_linearCombination K g b c
  rw [he] at hm
  exact hm

theorem exists_sparse_cut_basis {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (b : Module.Basis J K E) (f : E →ₗ[K] V) (g : E →ₗ[K] (A →₀ K)) (ℓ : ℕ)
    (hphysical : ∀ j, (g (b j)).support.card ≤ ℓ) :
    ∃ (I : Type (max u w)) (bcut : Module.Basis I K (LinearMap.ker f)),
      ∀ i, (g (bcut i).val).support.card ≤ ℓ * (Module.finrank K V + 1) := by
  classical
  let f₀ := f.comp b.repr.symm.toLinearMap
  obtain ⟨I, b₀, hsupport⟩ := SparseKernelBasis.exists_sparse_kernel_basis f₀
  let bcut := b₀.map (coordinateKernelEquiv b f)
  refine ⟨I, bcut, ?_⟩
  intro i
  change (g ((b₀.map (coordinateKernelEquiv b f)) i).val).support.card ≤ _
  rw [Module.Basis.map_apply, coordinateKernelEquiv_apply, physical_combination]
  exact (LinearCombinationSupport.card_le (fun j ↦ g (b j)) (b₀ i).val ℓ hphysical).trans
    (Nat.mul_le_mul_left ℓ (hsupport i))

theorem finite_equations {P : Type*} [Fintype P] (b : Module.Basis J K E)
    (f : E →ₗ[K] (P → K)) (g : E →ₗ[K] (A →₀ K)) (ℓ : ℕ)
    (hphysical : ∀ j, (g (b j)).support.card ≤ ℓ) :
    ∃ (I : Type (max u w)) (bcut : Module.Basis I K (LinearMap.ker f)),
      ∀ i, (g (bcut i).val).support.card ≤ ℓ * (Fintype.card P + 1) := by
  simpa only [Module.finrank_fintype_fun_eq_card] using exists_sparse_cut_basis b f g ℓ hphysical

end PaperP1.SparseConstraintBasis
