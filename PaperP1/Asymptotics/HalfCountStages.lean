module

public import PaperP1.Arithmetic.ChosenWindowWitness
public import PaperP1.Asymptotics.HalfCountExceptionalSets
public import PaperP1.Combinatorics.FiniteStageCounts

/-! # Actual decreasing stages for fixed witnesses in the conditional half-count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountStages

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountExceptionalSets

def exceptionalLists {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (lists G W old).filter fun n ↦ ∃ i, n i ∈ smallKernelCentres G N W

def largeCount (N : ℕ) (Y : ℝ) (x : ℕ) (A : Finset ℤ) : ℕ :=
  (A.filter fun a ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
    (PaperP1.RankinSmallKernel.truncatedKernel Y (PaperP1.LinearKernelFibres.value x a) : ℝ)).card

def survivors {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ) (m t : ℕ)
    (Y : ℕ → ℝ) (j : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact Nat.rec (lists G W old \ (shortLists G W old m ∪ exceptionalLists G N W old))
    (fun j S ↦ S.filter fun n ↦ ∀ i, m < (chosen W old n i).card → largeCount N (Y j) (n i) (chosen W old n i) < t) j

theorem survivors_zero {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ) (m t : ℕ) (Y : ℕ → ℝ) :
    survivors (r := r) G N W old m t Y 0 = lists G W old \ (shortLists G W old m ∪ exceptionalLists G N W old) := rfl

theorem survivors_succ {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) :
    survivors (r := r) G N W old m t Y (j + 1) = (survivors (r := r) G N W old m t Y j).filter fun n ↦
      ∀ i, m < (chosen W old n i).card → largeCount N (Y j) (n i) (chosen W old n i) < t := rfl

theorem survivors_succ_subset {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) :
    survivors (r := r) G N W old m t Y (j + 1) ⊆ survivors (r := r) G N W old m t Y j := filter_subset _ _

theorem survivors_subset_zero {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) : survivors (r := r) G N W old m t Y j ⊆ survivors (r := r) G N W old m t Y 0 := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih => exact (survivors_succ_subset G N W old m t j Y).trans ih

theorem survivor_data {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) (n : Fin r → ℕ) (hn : n ∈ survivors (r := r) G N W old m t Y j) :
    n ∈ lists G W old ∧ n ∉ shortLists G W old m ∧ ∀ i, n i ∉ smallKernelCentres G N W := by
  classical
  have hzero := (survivors_subset_zero G N W old m t j Y) hn
  obtain ⟨hnL, hnot⟩ := mem_sdiff.mp hzero
  refine ⟨hnL, (fun hshort ↦ hnot (mem_union_left _ hshort)), ?_⟩
  intro i hi
  exact hnot (mem_union_right _ (mem_filter.mpr ⟨hnL, i, hi⟩))

theorem survivor_few_large {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) (n : Fin r → ℕ) (hn : n ∈ survivors (r := r) G N W old m t Y (j + 1))
    (i : Fin r) (hi : m < (chosen W old n i).card) :
    largeCount N (Y j) (n i) (chosen W old n i) < t := (mem_filter.mp hn).2 i hi

theorem removed_source {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) (n : Fin r → ℕ)
    (hn : n ∈ survivors (r := r) G N W old m t Y j \ survivors (r := r) G N W old m t Y (j + 1)) :
    ∃ i, m < (chosen W old n i).card ∧ t ≤ largeCount N (Y j) (n i) (chosen W old n i) := by
  classical
  obtain ⟨hnS, hnot⟩ := mem_sdiff.mp hn
  have hfail : ¬∀ i, m < (chosen W old n i).card → largeCount N (Y j) (n i) (chosen W old n i) < t :=
    fun h ↦ hnot (mem_filter.mpr ⟨hnS, h⟩)
  simpa only [not_forall, not_lt, exists_prop] using hfail

end PaperP1.HalfCountStages
