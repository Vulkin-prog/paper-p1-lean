module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Separation.Basic

/-! # An actual open interval avoiding a finite point set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSetAvoidingInterval

open Set Filter
open scoped Topology

theorem exists_interval {X : Type*} [TopologicalSpace X] [T1Space X]
    (ζ : ℝ → X) (t₀ : ℝ) (s : Set ℝ) (hs : s ∈ 𝓝 t₀)
    (hc : ContinuousAt ζ t₀) (E : Finset X) (hnot : ζ t₀ ∉ E) :
    ∃ a b : ℝ, t₀ ∈ Ioo a b ∧ Ioo a b ⊆ s ∧ ∀ t ∈ Ioo a b, ζ t ∉ E := by
  classical
  have hclosed : IsClosed (E : Set X) := E.finite_toSet.isClosed
  have hn : {t : ℝ | ζ t ∉ E} ∈ 𝓝 t₀ :=
    hc.tendsto.eventually (hclosed.isOpen_compl.mem_nhds hnot)
  obtain ⟨a, b, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (Filter.inter_mem hs hn)
  exact ⟨a, b, hmem, (fun t ht ↦ (hsub ht).1), (fun t ht ↦ (hsub ht).2)⟩

end PaperP1.FiniteSetAvoidingInterval
