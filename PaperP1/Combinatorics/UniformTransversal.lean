module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Lean.Elab.Tactic.Omega

/-! # A small transversal from the absence of a disjoint matching -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformTransversal

open Finset

variable {V : Type*} [DecidableEq V]

theorem exists_transversal (F : Finset (Finset V)) (j t : ℕ) (hj : 1 ≤ j)
    (hcard : ∀ A ∈ F, A.card = j)
    (hno : ∀ E ⊆ F, E.card = t → ¬(↑E : Set (Finset V)).PairwiseDisjoint id) :
    ∃ H : Finset V, H ⊆ F.biUnion id ∧ H.card ≤ j * (t - 1) ∧
      ∀ A ∈ F, (A ∩ H).Nonempty := by
  classical
  let C := F.powerset.filter fun E : Finset (Finset V) ↦ (↑E : Set (Finset V)).PairwiseDisjoint id
  have hzero : (∅ : Finset (Finset V)) ∈ C := by simp [C]
  obtain ⟨E, hEC, hmax⟩ := exists_max_image C Finset.card ⟨∅, hzero⟩
  obtain ⟨hEF, hdisj⟩ := mem_filter.mp hEC
  have hEF' : E ⊆ F := mem_powerset.mp hEF
  have hEt : E.card < t := by
    by_contra h
    obtain ⟨T, hTE, hTcard⟩ := exists_subset_card_eq (Nat.le_of_not_gt h)
    exact hno T (hTE.trans hEF') hTcard (Set.Pairwise.mono hTE hdisj)
  let H := E.biUnion id
  have hHF : H ⊆ F.biUnion id := by
    intro v hv
    obtain ⟨A, hAE, hvA⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨A, hEF' hAE, hvA⟩
  have hHcard : H.card ≤ j * (t - 1) := by
    calc
      _ = ∑ A ∈ E, A.card := card_biUnion hdisj
      _ = E.card * j := by
        rw [sum_congr rfl (fun A hA ↦ hcard A (hEF' hA))]
        simp
      _ ≤ (t - 1) * j := Nat.mul_le_mul_right _ (by omega)
      _ = _ := Nat.mul_comm _ _
  refine ⟨H, hHF, hHcard, ?_⟩
  intro A hAF
  by_contra hnot
  have hAH : Disjoint A H := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnot)
  have hAold (B : Finset V) (hBE : B ∈ E) : Disjoint A B := by
    apply disjoint_left.mpr
    intro v hvA hvB
    exact disjoint_left.mp hAH hvA (mem_biUnion.mpr ⟨B, hBE, hvB⟩)
  have hAE : A ∉ E := by
    intro hAE
    have hself := hAold A hAE
    have hnonempty : A.Nonempty := card_pos.mp (by rw [hcard A hAF]; omega)
    obtain ⟨v, hv⟩ := hnonempty
    exact disjoint_left.mp hself hv hv
  have hnextDisj : (↑(insert A E) : Set (Finset V)).PairwiseDisjoint id := by
    intro B hB D hD hBD
    change B ∈ insert A E at hB
    change D ∈ insert A E at hD
    rcases mem_insert.mp hB with hBA | hBE
    · rcases mem_insert.mp hD with hDA | hDE
      · exact False.elim (hBD (hBA.trans hDA.symm))
      · rw [hBA]
        exact hAold D hDE
    · rcases mem_insert.mp hD with hDA | hDE
      · rw [hDA]
        exact (hAold B hBE).symm
      · exact hdisj hBE hDE hBD
  have hnext : insert A E ∈ C := by
    apply mem_filter.mpr
    exact ⟨mem_powerset.mpr (insert_subset hAF hEF'), hnextDisj⟩
  have hcontra := hmax (insert A E) hnext
  rw [card_insert_of_notMem hAE] at hcontra
  omega

end PaperP1.UniformTransversal
