module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-! # A ternary relation missing a block vanishes under pairwise directness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPairwiseRigidity

variable {K U : Type*} [Ring K] [AddCommGroup U] [Module K U]

theorem disjoint_sum_zero {S T : Submodule K U} (hST : Disjoint S T) {u v : U}
    (hu : u ∈ S) (hv : v ∈ T) (hsum : u + v = 0) : u = 0 ∧ v = 0 := by
  have heq : u = -v := eq_neg_of_add_eq_zero_left hsum
  have huT : u ∈ T := by rw [heq]; exact T.neg_mem hv
  have hu0 := (Submodule.disjoint_def.mp hST) u hu huT
  exact ⟨hu0, by simpa only [hu0, zero_add] using hsum⟩

theorem ternary_missing_zero (S : Fin 3 → Submodule K U)
    (hS : Pairwise (fun i j ↦ Disjoint (S i) (S j))) (g : Fin 3 → U)
    (hmem : ∀ i, g i ∈ S i) (hsum : (∑ i, g i) = 0) (k : Fin 3) (hk : g k = 0) :
    ∀ i, g i = 0 := by
  rw [Fin.sum_univ_three] at hsum
  fin_cases k
  · change g 0 = 0 at hk
    have h12 : g 1 + g 2 = 0 := by simpa only [hk, zero_add] using hsum
    obtain ⟨h1, h2⟩ := disjoint_sum_zero (hS (by decide : (1 : Fin 3) ≠ 2)) (hmem 1) (hmem 2) h12
    intro i
    fin_cases i
    · exact hk
    · exact h1
    · exact h2
  · change g 1 = 0 at hk
    have h02 : g 0 + g 2 = 0 := by simpa only [hk, add_zero] using hsum
    obtain ⟨h0, h2⟩ := disjoint_sum_zero (hS (by decide : (0 : Fin 3) ≠ 2)) (hmem 0) (hmem 2) h02
    intro i
    fin_cases i
    · exact h0
    · exact hk
    · exact h2
  · change g 2 = 0 at hk
    have h01 : g 0 + g 1 = 0 := by simpa only [hk, add_zero] using hsum
    obtain ⟨h0, h1⟩ := disjoint_sum_zero (hS (by decide : (0 : Fin 3) ≠ 1)) (hmem 0) (hmem 1) h01
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact hk

end PaperP1.TernaryPairwiseRigidity
