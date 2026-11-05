module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Data.Finset.Insert

/-! # Actual finite representatives of the components meeting a finite population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteComponentRepresentatives

open Set

theorem disjoint_of_ne {X : Type*} [TopologicalSpace X] (F : Set X) (a b : X)
    (hne : connectedComponentIn F a ≠ connectedComponentIn F b) :
    Disjoint (connectedComponentIn F a) (connectedComponentIn F b) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  exact hne ((connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm)

theorem disjoint_of_not_mem {X : Type*} [TopologicalSpace X] (F : Set X) (a b : X)
    (ha : a ∈ F) (hnot : a ∉ connectedComponentIn F b) :
    Disjoint (connectedComponentIn F a) (connectedComponentIn F b) := by
  apply disjoint_of_ne F a b
  intro he
  exact hnot (he ▸ mem_connectedComponentIn ha)

theorem exists_representatives {X : Type*} [TopologicalSpace X] (F : Set X) (S : Finset X)
    (hS : ∀ z ∈ S, z ∈ F) :
    ∃ I : Finset X, I ⊆ S ∧
      (∀ a ∈ I, ∀ b ∈ I, a ≠ b → Disjoint (connectedComponentIn F a) (connectedComponentIn F b)) ∧
      ∀ z ∈ S, ∃ a ∈ I, z ∈ connectedComponentIn F a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert z S hz ih =>
    obtain ⟨I, hIS, hdisj, hcover⟩ := ih (fun w hw ↦ hS w (Finset.mem_insert_of_mem hw))
    by_cases hcovered : ∃ a ∈ I, z ∈ connectedComponentIn F a
    · refine ⟨I, fun a ha ↦ Finset.mem_insert_of_mem (hIS ha), hdisj, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hcovered
      · exact hcover w hw
    · have hzF := hS z (Finset.mem_insert_self _ _)
      have hsep (b : X) (hb : b ∈ I) :
          Disjoint (connectedComponentIn F z) (connectedComponentIn F b) :=
        disjoint_of_not_mem F z b hzF (fun hm ↦ hcovered ⟨b, hb, hm⟩)
      refine ⟨insert z I, ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hIS ha)
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with haz | haI
        · have hbI : b ∈ I := (Finset.mem_insert.mp hb).resolve_left
            (fun hbz ↦ hab (haz.trans hbz.symm))
          rw [haz]
          exact hsep b hbI
        · rcases Finset.mem_insert.mp hb with hbz | hbI
          · rw [hbz]
            exact (hsep a haI).symm
          · exact hdisj a haI b hbI hab
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwz | hwS
        · refine ⟨z, Finset.mem_insert_self _ _, ?_⟩
          rw [hwz]
          exact mem_connectedComponentIn hzF
        · obtain ⟨a, ha, hwa⟩ := hcover w hwS
          exact ⟨a, Finset.mem_insert_of_mem ha, hwa⟩

end PaperP1.FiniteComponentRepresentatives
