module

public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Affine.ConnectedRelations

/-! # Canonically connected actual finite effective blocks participate in relations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedBlockLists

open Finset PaperP1.Arithmetic

def Connected {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) : Prop :=
  PaperP1.Affine.canonicalRelationPartition (fun i ↦ PaperP1.FiniteEvenSquareClasses.space (blocks i (n i))) = ⊤

def population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦ Function.Injective n ∧ Connected blocks n

theorem mem_population {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ) :
    n ∈ population G blocks ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧ Connected blocks n := by
  classical
  simp only [population, mem_filter, Fintype.mem_piFinset]

theorem covered_of_connected {r : ℕ} (blocks : Fin r → ℕ → Finset ℕ) (n : Fin r → ℕ)
    (hr : 2 ≤ r) (hconnected : Connected blocks n) :
    PaperP1.RelativeBlockRelations.Covered blocks ∅ n := by
  intro i
  have hex : ∃ j : Fin r, i ≠ j := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro hij
      have hval := congrArg Fin.val hij
      change i.val = 1 at hval
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro hij
      have hval := congrArg Fin.val hij
      change i.val = 0 at hval
      omega
  obtain ⟨j, hij⟩ := hex
  let S := fun k ↦ PaperP1.FiniteEvenSquareClasses.space (blocks k (n k))
  obtain ⟨s, hs, hne⟩ := PaperP1.ConnectedRelations.coordinate_relation S hconnected i j hij
  refine ⟨fun k ↦ (s k).val, (fun k ↦ (s k).property), hne, ?_⟩
  change PaperP1.Affine.relationAddition S s ∈ PaperP1.OldSpaceProjection.oldSpace ∅
  rw [hs]
  exact Submodule.zero_mem _

theorem population_subset_covered {r : ℕ} (G : Finset ℕ) (blocks : Fin r → ℕ → Finset ℕ) (hr : 2 ≤ r) :
    population G blocks ⊆ PaperP1.RelativeBlockRelations.population G blocks ∅ := by
  intro n hn
  obtain ⟨hnG, hinj, hconnected⟩ := (mem_population G blocks n).mp hn
  exact (PaperP1.RelativeBlockRelations.mem_population G blocks ∅ n).mpr
    ⟨hnG, hinj, covered_of_connected blocks n hr hconnected⟩

end PaperP1.ConnectedBlockLists
