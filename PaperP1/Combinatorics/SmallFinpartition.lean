module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-! # A partition of at most three elements without singleton parts is indiscrete -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallFinpartition

open Finset

theorem eq_top_without_singletons {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (hI : I.Nonempty) (hcard : I.card ≤ 3) (P : Finpartition I)
    (hparts : ∀ C ∈ P.parts, C.card ≠ 1) : P = ⊤ := by
  classical
  have hlower : 2 * P.parts.card ≤ I.card := by
    calc
      _ = ∑ _C ∈ P.parts, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ C ∈ P.parts, C.card := by
        apply sum_le_sum
        intro C hC
        have hpos : 0 < C.card := card_pos.mpr (nonempty_iff_ne_empty.mpr (P.ne_bot hC))
        have hne := hparts C hC
        omega
      _ = _ := P.sum_card_parts
  have hnonempty := P.parts_nonempty hI.ne_empty
  have hcount : P.parts.card = 1 := by
    have hpos := card_pos.mpr hnonempty
    omega
  obtain ⟨C, hC⟩ := card_eq_one.mp hcount
  have hCI : C = I := by
    have h := P.sup_parts
    rw [hC, sup_singleton] at h
    exact h
  have hmem : I ∈ P.parts := by rw [hC]; exact mem_singleton.mpr hCI.symm
  apply top_le_iff.mp
  intro D hD
  exact ⟨I, hmem, (⊤ : Finpartition I).le hD⟩

end PaperP1.SmallFinpartition
