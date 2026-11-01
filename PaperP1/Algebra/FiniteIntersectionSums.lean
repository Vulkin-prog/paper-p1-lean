module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Restrict a literal finite sum to an intersection when all absent coefficients vanish -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteIntersectionSums

open Finset

theorem restrict_sum {α E : Type*} [DecidableEq α] [AddCommMonoid E]
    (S T : Finset α) (f : S → E) (hzero : ∀ n : S, n.val ∉ T → f n = 0) :
    (∑ n : ↥(S ∩ T), f ⟨n.val, (mem_inter.mp n.property).1⟩) = ∑ n : S, f n := by
  classical
  let A : Finset S := univ.filter fun n ↦ n.val ∈ T
  calc
    _ = ∑ n ∈ A, f n := by
      apply sum_bij (fun n _ ↦ (⟨n.val, (mem_inter.mp n.property).1⟩ : S))
      · intro n _
        exact mem_filter.mpr ⟨mem_univ _, (mem_inter.mp n.property).2⟩
      · intro n _ m _ heq
        exact Subtype.ext (congrArg (fun v : S ↦ v.val) heq)
      · intro n hn
        exact ⟨⟨n.val, mem_inter.mpr ⟨n.property, (mem_filter.mp hn).2⟩⟩, mem_univ _, rfl⟩
      · intro n _
        rfl
    _ = ∑ n : S, f n := by
      apply sum_subset (subset_univ A)
      intro n _ hn
      exact hzero n (fun h ↦ hn (mem_filter.mpr ⟨mem_univ _, h⟩))

end PaperP1.FiniteIntersectionSums
