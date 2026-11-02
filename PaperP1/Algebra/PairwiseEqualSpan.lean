module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.Push

/-! # Pairwise equal nonzero images span at most one dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairwiseEqualSpan

theorem exists_line {K M ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
    (v : ι → M) (hpair : ∀ i j, v i = 0 ∨ v j = 0 ∨ v i = v j) :
    ∃ a : M, Submodule.span K (Set.range v) ≤ Submodule.span K {a} := by
  by_cases hz : ∀ i, v i = 0
  · refine ⟨0, Submodule.span_le.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    rw [hz i]
    exact Submodule.zero_mem _
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    refine ⟨v i, Submodule.span_le.mpr ?_⟩
    rintro _ ⟨j, rfl⟩
    rcases hpair i j with h | h | h
    · exact (hi h).elim
    · rw [h]
      exact Submodule.zero_mem _
    · rw [← h]
      exact Submodule.subset_span (Set.mem_singleton _)

theorem finrank_le_one {K M ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
    (v : ι → M) (hpair : ∀ i j, v i = 0 ∨ v j = 0 ∨ v i = v j) :
    Module.finrank K (Submodule.span K (Set.range v)) ≤ 1 := by
  obtain ⟨a, hspan⟩ := exists_line (K := K) v hpair
  let : Module.Finite K (Submodule.span K ({a} : Set M)) :=
    Module.Finite.span_of_finite K (Set.finite_singleton a)
  exact (Submodule.finrank_mono hspan).trans (by
    simpa using finrank_span_le_ncard (R := K) ({a} : Set M) (Set.finite_singleton a))

end PaperP1.PairwiseEqualSpan
