module

public import PaperP1.Combinatorics.SmallFinpartition

/-! # A four-element partition without singleton parts is one block or two pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourFinpartition

open Finset

theorem top_or_two_pairs {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (hcard : I.card = 4) (P : Finpartition I) (hparts : ∀ C ∈ P.parts, C.card ≠ 1) :
    P = ⊤ ∨ ∃ C D : Finset ι, C ≠ D ∧ P.parts = {C, D} ∧ C.card = 2 ∧ D.card = 2 := by
  classical
  have hI : I.Nonempty := card_pos.mp (by omega)
  have hlower : 2 * P.parts.card ≤ I.card := by
    calc
      _ = ∑ _C ∈ P.parts, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ C ∈ P.parts, C.card := by
        apply sum_le_sum
        intro C hC
        have hpos : 0 < C.card := card_pos.mpr (P.nonempty_of_mem_parts hC)
        have hne := hparts C hC
        omega
      _ = _ := P.sum_card_parts
  have hpos : 0 < P.parts.card := card_pos.mpr (P.parts_nonempty hI.ne_empty)
  by_cases hone : P.parts.card = 1
  · left
    obtain ⟨C, hC⟩ := card_eq_one.mp hone
    have hCI : C = I := by
      have h := P.sup_parts
      rw [hC, sup_singleton] at h
      exact h
    have hmem : I ∈ P.parts := by rw [hC]; exact mem_singleton.mpr hCI.symm
    apply top_le_iff.mp
    intro D hD
    exact ⟨I, hmem, (⊤ : Finpartition I).le hD⟩
  · right
    have htwo : P.parts.card = 2 := by omega
    obtain ⟨C, D, hCD, hP⟩ := card_eq_two.mp htwo
    have hC : C ∈ P.parts := by rw [hP]; exact mem_insert_self _ _
    have hD : D ∈ P.parts := by rw [hP]; exact mem_insert_of_mem (mem_singleton_self _)
    have hcpos := card_pos.mpr (P.nonempty_of_mem_parts hC)
    have hdpos := card_pos.mpr (P.nonempty_of_mem_parts hD)
    have hcne := hparts C hC
    have hdne := hparts D hD
    have hs := P.sum_card_parts
    rw [hP, sum_pair hCD, hcard] at hs
    exact ⟨C, D, hCD, hP, by omega, by omega⟩

end PaperP1.FourFinpartition
