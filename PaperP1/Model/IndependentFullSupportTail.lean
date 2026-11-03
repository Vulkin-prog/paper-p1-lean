module

public import PaperP1.Model.RelativeWindowFamilies

/-! # Literal actual full-support families with independent heterogeneous weights at all cardinalities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentFullSupportTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

def FullSupport (L : ℕ) (I : Finset ℕ) : Prop :=
  ∃ u : (i : I) → squareClassSpace i.val L, (∀ i, u i ≠ 0) ∧ (∑ i : I, (u i).val) = 0

def families (G : Finset ℕ) (L s : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun I ↦ s ≤ I.card ∧ FullSupport L I

def mass (G : Finset ℕ) (L s : ℕ) (v : ℝ) : ℝ :=
  ∑ I ∈ families G L s, ∏ x ∈ I, v * infiniteMarginal x L

theorem mem_families (G I : Finset ℕ) (L s : ℕ) :
    I ∈ families G L s ↔ I ⊆ G ∧ s ≤ I.card ∧ FullSupport L I := by
  classical
  simp only [families, mem_filter, mem_powerset]

theorem witnesses (L : ℕ) (I : Finset ℕ) (hfull : FullSupport L I) :
    RelativeWindowFamilies.Witnesses L ⊥ I := by
  obtain ⟨u, hu, hsum⟩ := hfull
  intro i
  refine ⟨u, hu i, ?_⟩
  rw [hsum]
  exact Submodule.zero_mem _

theorem primitive_fullSupport (L : ℕ) (I : Finset ℕ) (hprim : ConnectedWindowFamilies.Primitive L I) :
    FullSupport L I :=
  PrimitiveRelations.full_relation_of_minimal_nullity (fun x ↦ squareClassSpace x L) I hprim.1 hprim.2

end PaperP1.IndependentFullSupportTail
