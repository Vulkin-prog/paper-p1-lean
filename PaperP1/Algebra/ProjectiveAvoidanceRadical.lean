module

public import PaperP1.Geometry.ProjectiveAvoidanceCone
public import Mathlib.RingTheory.Nullstellensatz
public import Lean.Elab.Tactic.Omega

/-! # Actual projective avoidance forces powers of every cone coordinate into the parameter ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveAvoidanceRadical

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]
  (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
  {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e)
  (ℓ : MvPolynomial σ F) (hℓ : ℓ.IsHomogeneous 1)
  (havoid : ∀ p ∈ ProjectiveSectionFiniteSet.sectionLocus I f, eval p.rep ℓ ≠ 0)

include hI hf hℓ havoid in
omit [IsAlgClosed F] [Finite σ] in
theorem zero_locus_subset :
    zeroLocus F (I ⊔ Ideal.span {f, ℓ}) ⊆ ({0} : Set (σ → F)) := by
  intro w hw
  have hleft : I ≤ I ⊔ Ideal.span {f, ℓ} := le_sup_left
  have hright : Ideal.span {f, ℓ} ≤ I ⊔ Ideal.span {f, ℓ} := le_sup_right
  have hcurve : ∀ P ∈ I, eval w P = 0 := fun P hP ↦ hw P (hleft hP)
  have hfone : f ∈ I ⊔ Ideal.span {f, ℓ} := hright (Ideal.subset_span (by simp))
  have hℓone : ℓ ∈ I ⊔ Ideal.span {f, ℓ} := hright (Ideal.subset_span (by simp))
  exact ProjectiveAvoidanceCone.common_zero I hI f hf ℓ hℓ havoid w hcurve (hw f hfone) (hw ℓ hℓone)

include hI hf hℓ havoid in
theorem variable_mem_radical (i : σ) :
    X i ∈ (I ⊔ Ideal.span {f, ℓ}).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := F)]
  intro w hw
  have he : w = 0 := zero_locus_subset I hI f hf ℓ hℓ havoid hw
  subst w
  simp

include hI hf hℓ havoid in
theorem exists_uniform_power :
    ∃ N : ℕ, 0 < N ∧ ∀ i : σ, (X i) ^ N ∈ I ⊔ Ideal.span {f, ℓ} := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hpower (i : σ) : ∃ m : ℕ, (X i) ^ m ∈ I ⊔ Ideal.span {f, ℓ} :=
    variable_mem_radical I hI f hf ℓ hℓ havoid i
  choose m hm using hpower
  let N := Finset.univ.sup m + 1
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro i
  have hle : m i ≤ N := (Finset.le_sup (f := m) (Finset.mem_univ i)).trans (Nat.le_add_right _ 1)
  have he : (X i : MvPolynomial σ F) ^ N = (X i) ^ (N - m i) * (X i) ^ m i := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [he]
  exact Ideal.mul_mem_left _ _ (hm i)

end PaperP1.ProjectiveAvoidanceRadical
