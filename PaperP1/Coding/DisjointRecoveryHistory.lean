module

public import PaperP1.Coding.SequentialRankBudget
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Function.Basic

/-! # Constructing a maximal finite history of bad disjoint recoveries

Each new direction is independent of its predecessors. The length is bounded
by the ambient dimension, so a finite maximum supplies a stopping history.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointRecoveryHistory

open Finset Submodule PaperP1.SequentialRankBudget

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]

local instance recoveryHistoryDecidableEq : DecidableEq U := Classical.decEq _

def IsStep (L : V → U) (d t : ℕ) (a : ℕ → U) (A : ℕ → Fin t → Finset V) (i : ℕ) : Prop :=
  a i ∉ prefixSpan (K := K) a i ∧
  (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint (A i) ∧
  (∀ j : Fin t, 1 ≤ (A i j).card ∧ (A i j).card ≤ d) ∧
  (∀ j : Fin t, a i - (∑ v ∈ A i j, L v) ∈ prefixSpan (K := K) a i)

def IsHistory (L : V → U) (d t : ℕ) (a : ℕ → U) (A : ℕ → Fin t → Finset V) (m : ℕ) : Prop :=
  ∀ i < m, IsStep (K := K) L d t a A i

def HasBadRecoveries (L : V → U) (d t : ℕ) (W : Submodule K U) : Prop :=
  ∃ α : U, α ∉ W ∧ ∃ A : Fin t → Finset V,
    (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint A ∧
    (∀ j : Fin t, 1 ≤ (A j).card ∧ (A j).card ≤ d) ∧
    ∀ j : Fin t, α - (∑ v ∈ A j, L v) ∈ W

theorem history_length_le (L : V → U) (d t : ℕ) (a : ℕ → U)
    (A : ℕ → Fin t → Finset V) (m : ℕ) (h : IsHistory (K := K) L d t a A m) :
    m ≤ Module.finrank K U :=
  chain_length_le_dimension a m (fun i hi ↦ (h i hi).1)

omit [FiniteDimensional K U] in
theorem prefixSpan_update (a : ℕ → U) (m i : ℕ) (α : U) (hi : i ≤ m) :
    prefixSpan (K := K) (Function.update a m α) i = prefixSpan a i := by
  classical
  have heq : (range i).image (Function.update a m α) = (range i).image a := by
    apply image_congr
    intro j hj
    have hne : j ≠ m := by have h := mem_range.mp hj; omega
    exact Function.update_of_ne hne _ _
  unfold prefixSpan
  rw [heq]

omit [FiniteDimensional K U] in
theorem history_extend (L : V → U) (d t : ℕ) (a : ℕ → U)
    (A : ℕ → Fin t → Finset V) (m : ℕ) (h : IsHistory (K := K) L d t a A m)
    (α : U) (hα : α ∉ prefixSpan (K := K) a m) (B : Fin t → Finset V)
    (hdisj : (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint B)
    (hcard : ∀ j : Fin t, 1 ≤ (B j).card ∧ (B j).card ≤ d)
    (hrec : ∀ j : Fin t, α - (∑ v ∈ B j, L v) ∈ prefixSpan (K := K) a m) :
    IsHistory (K := K) L d t (Function.update a m α) (Function.update A m B) (m + 1) := by
  intro i hi
  by_cases him : i < m
  · have hne : i ≠ m := by omega
    have hprefix := prefixSpan_update (K := K) a m i α him.le
    have hiStep := h i him
    simpa only [IsStep, Function.update_of_ne hne, hprefix] using hiStep
  · have heq : i = m := by omega
    subst i
    have hprefix := prefixSpan_update (K := K) a m m α le_rfl
    simp only [IsStep, Function.update_self, hprefix]
    exact ⟨hα, hdisj, hcard, hrec⟩

theorem exists_maximal_history (L : V → U) (d t : ℕ) :
    ∃ (m : ℕ) (a : ℕ → U) (A : ℕ → Fin t → Finset V),
      IsHistory (K := K) L d t a A m ∧ ¬ HasBadRecoveries L d t (prefixSpan (K := K) a m) := by
  classical
  let C := (range (Module.finrank K U + 1)).filter fun m ↦
    ∃ (a : ℕ → U) (A : ℕ → Fin t → Finset V), IsHistory (K := K) L d t a A m
  have hzero : 0 ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.zero_lt_succ _), (fun _ ↦ 0), (fun _ _ ↦ ∅), ?_⟩
    intro i hi
    omega
  obtain ⟨m, hm, hmax⟩ := exists_max_image C id ⟨0, hzero⟩
  obtain ⟨a, A, hhistory⟩ := (mem_filter.mp hm).2
  refine ⟨m, a, A, hhistory, ?_⟩
  intro hbad
  obtain ⟨α, hα, B, hdisj, hcard, hrec⟩ := hbad
  have hnext := history_extend L d t a A m hhistory α hα B hdisj hcard hrec
  have hbound := history_length_le L d t _ _ _ hnext
  have hmem : m + 1 ∈ C := mem_filter.mpr
    ⟨mem_range.mpr (Nat.lt_succ_of_le hbound), _, _, hnext⟩
  have hcontra := hmax (m + 1) hmem
  change m + 1 ≤ m at hcontra
  omega

end PaperP1.DisjointRecoveryHistory
