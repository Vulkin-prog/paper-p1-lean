module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # A finite module on a graded algebra has a finite homogeneous generating family -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v w

namespace PaperP1.FiniteHomogeneousModuleGenerators

open DirectSum

theorem exists_generators {F : Type u} {A : Type v} {B : Type w}
    [CommRing F] [CommRing A] [CommRing B] [Algebra F B] [Module A B] [Module.Finite A B]
    (H : ℕ → Submodule F B) [GradedAlgebra H] :
    ∃ (ι : Type w) (_ : Fintype ι) (v : ι → B) (d : ι → ℕ),
      (∀ i, v i ∈ H (d i)) ∧ Submodule.span A (Set.range v) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  let ι := Σ j : S, {n : ℕ // n ∈ (decompose H (j : B)).support}
  let v (i : ι) : B := decompose H (i.1 : B) i.2
  let d (i : ι) : ℕ := i.2
  have hspan : Submodule.span A (S : Set B) ≤ Submodule.span A (Set.range v) := by
    apply Submodule.span_le.mpr
    intro b hb
    rw [← sum_support_decompose H b]
    apply Submodule.sum_mem
    intro n hn
    exact Submodule.subset_span ⟨⟨⟨b, hb⟩, ⟨n, hn⟩⟩, rfl⟩
  refine ⟨ι, inferInstance, v, d, fun i ↦ (decompose H (i.1 : B) i.2).property, ?_⟩
  exact top_unique (hS ▸ hspan)

end PaperP1.FiniteHomogeneousModuleGenerators
