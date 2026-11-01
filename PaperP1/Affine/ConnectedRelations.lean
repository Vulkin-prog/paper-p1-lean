module

public import PaperP1.Affine.DirectPartitions

/-! # A connected canonical direct component has a relation at every coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedRelations

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]

theorem coordinate_relation (S : ι → Submodule 𝔽₂ U)
    (hconnected : canonicalRelationPartition S = ⊤) (i j : ι) (hij : i ≠ j) :
    ∃ s : (k : ι) → S k, relationAddition S s = 0 ∧ (s i).val ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ s : (k : ι) → S k, relationAddition S s = 0 → (s i).val = 0 := by
    intro s hs
    by_contra hsi
    exact hnone ⟨s, hs, hsi⟩
  let B := (univ : Finset ι) \ {i}
  have hB : B ≠ ⊥ := by
    have hnonempty : B.Nonempty := ⟨j, mem_sdiff.mpr ⟨mem_univ _, by simpa only [mem_singleton] using hij.symm⟩⟩
    exact hnonempty.ne_empty
  have hdisjoint : Disjoint ({i} : Finset ι) B := by
    apply disjoint_left.mpr
    intro x hxi hxB
    exact (mem_sdiff.mp hxB).2 hxi
  have hcover : ({i} : Finset ι) ⊔ B = univ := by
    ext x
    by_cases hx : x = i <;> simp [B, hx]
  let Q : Finpartition ({i} : Finset ι) := ⊤
  let P : Finpartition (univ : Finset ι) := Q.extend hB hdisjoint hcover
  have hP : RelationDirectPartition S P := by
    intro s hs C hC
    change C ∈ insert B Q.parts at hC
    rcases mem_insert.mp hC with rfl | hCQ
    · have hsum := sum_sdiff (f := fun k ↦ (s k).val) (subset_univ ({i} : Finset ι))
      rw [sum_singleton, hzero s hs, add_zero] at hsum
      exact hsum.trans hs
    · have hCeq : C = {i} := mem_singleton.mp (Finpartition.parts_top_subset ({i} : Finset ι) hCQ)
      rw [hCeq, sum_singleton]
      exact hzero s hs
  have htop : P = ⊤ := top_le_iff.mp (by
    simpa only [hconnected] using canonicalRelationPartition_le S P hP)
  have hiQ : ({i} : Finset ι) ∈ Q.parts := by
    obtain ⟨C, hC, _⟩ := Q.exists_mem (mem_singleton_self i)
    have hCeq : C = {i} := mem_singleton.mp (Finpartition.parts_top_subset ({i} : Finset ι) hC)
    simpa only [hCeq] using hC
  have hiP : ({i} : Finset ι) ∈ P.parts := mem_insert_of_mem hiQ
  have hiTop : ({i} : Finset ι) ∈ (⊤ : Finpartition (univ : Finset ι)).parts := by
    simpa only [htop] using hiP
  have hsingle : ({i} : Finset ι) = univ := mem_singleton.mp
    (Finpartition.parts_top_subset (univ : Finset ι) hiTop)
  have hj : j ∈ ({i} : Finset ι) := by rw [hsingle]; exact mem_univ _
  exact hij (mem_singleton.mp hj).symm

end PaperP1.ConnectedRelations
