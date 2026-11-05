module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # A common positive level crossing on a finite family of connected sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedBarrierCrossing

open Set

theorem crossing {X : Type*} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f)
    (s : Set X) (hs : IsPreconnected s) (a : X) (ha : a ∈ s)
    (w : X) (hw : w ∈ closure s) (hfw : f w = 0)
    (ε : ℝ) (hε : 0 < ε) (haε : ε < f a) :
    ∃ z ∈ s, f z = ε := by
  have hopen : IsOpen {z | f z < ε} := isOpen_lt hf continuous_const
  obtain ⟨v, hvlow, hv⟩ := mem_closure_iff.mp hw _ hopen (by
    change f w < ε
    rw [hfw]
    exact hε)
  exact hs.intermediate_value hv ha hf.continuousOn ⟨hvlow.le, haε.le⟩

theorem common_positive_level {ι : Type*} (I : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ I, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ I, ε < f i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨ε, hε, hbound⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self _ _)
    refine ⟨min ε (f i / 2), lt_min hε (half_pos hfi), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (half_lt_self hfi)
    · exact (min_le_left _ _).trans_lt (hbound j hj)

end PaperP1.ConnectedBarrierCrossing
