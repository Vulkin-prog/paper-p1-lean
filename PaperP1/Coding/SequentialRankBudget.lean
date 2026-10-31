module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

/-! # A deterministic rank budget for sequential recoveries -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SequentialRankBudget

open Finset Submodule

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

local instance sequentialDecidableEq : DecidableEq U := Classical.decEq _

def prefixSpan (a : ℕ → U) (m : ℕ) : Submodule K U :=
  span K (↑((range m).image a) : Set U)

def failedSpan (a : ℕ → U) (p : ℕ → Prop) [DecidablePred p] (m : ℕ) : Submodule K U :=
  span K (↑(((range m).filter p).image a) : Set U)

theorem prefixSpan_zero (a : ℕ → U) : prefixSpan (K := K) a 0 = ⊥ := by
  simp [prefixSpan]

theorem prefixSpan_succ (a : ℕ → U) (m : ℕ) :
    prefixSpan (K := K) a (m + 1) = K ∙ a m ⊔ prefixSpan a m := by
  classical
  simp only [prefixSpan, range_add_one, image_insert, coe_insert, span_insert]

theorem failedSpan_mono (a : ℕ → U) (p : ℕ → Prop) [DecidablePred p]
    {m n : ℕ} (hmn : m ≤ n) : failedSpan (K := K) a p m ≤ failedSpan a p n := by
  classical
  apply span_mono
  exact image_subset_image (filter_subset_filter p (range_mono hmn))

theorem prefix_le_selected_and_failed (a : ℕ → U) (p : ℕ → Prop) [DecidablePred p]
    (S : Submodule K U) (m : ℕ)
    (hgood : ∀ i < m, ¬p i → a i ∈ S ⊔ prefixSpan (K := K) a i) :
    prefixSpan (K := K) a m ≤ S ⊔ failedSpan a p m := by
  classical
  induction m with
  | zero => rw [prefixSpan_zero]; exact bot_le
  | succ m ih =>
    let T := S ⊔ failedSpan (K := K) a p (m + 1)
    have hprev : prefixSpan (K := K) a m ≤ T :=
      (ih (fun i hi ↦ hgood i (Nat.lt_succ_of_lt hi))).trans
        (sup_le_sup_left (failedSpan_mono a p (Nat.le_succ m)) S)
    have hnew : a m ∈ T := by
      by_cases hp : p m
      · apply (le_sup_right : failedSpan (K := K) a p (m + 1) ≤ T)
        apply subset_span
        exact mem_image.mpr ⟨m, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self m), hp⟩, rfl⟩
      · have hsup : S ⊔ prefixSpan (K := K) a m ≤ T := sup_le le_sup_left hprev
        exact hsup (hgood m (Nat.lt_succ_self m) hp)
    rw [prefixSpan_succ]
    exact sup_le (span_le.mpr (Set.singleton_subset_iff.mpr hnew)) hprev

theorem prefix_dimension [FiniteDimensional K U] (a : ℕ → U) (m : ℕ)
    (hnew : ∀ i < m, a i ∉ prefixSpan (K := K) a i) :
    Module.finrank K (prefixSpan (K := K) a m) = m := by
  induction m with
  | zero => rw [prefixSpan_zero, finrank_bot]
  | succ m ih =>
    rw [prefixSpan_succ, sup_comm, Submodule.finrank_sup_span_singleton (hnew m (Nat.lt_succ_self m))]
    rw [ih (fun i hi ↦ hnew i (Nat.lt_succ_of_lt hi))]

theorem chain_length_le_dimension [FiniteDimensional K U] (a : ℕ → U) (m : ℕ)
    (hnew : ∀ i < m, a i ∉ prefixSpan (K := K) a i) : m ≤ Module.finrank K U := by
  rw [← prefix_dimension a m hnew]
  exact Submodule.finrank_le _

theorem failed_dimension_le (a : ℕ → U) (p : ℕ → Prop) [DecidablePred p] (m : ℕ) :
    Module.finrank K (failedSpan (K := K) a p m) ≤ ((range m).filter p).card := by
  classical
  exact (finrank_span_finset_le_card (((range m).filter p).image a)).trans card_image_le

theorem rank_budget [FiniteDimensional K U] (a : ℕ → U) (p : ℕ → Prop) [DecidablePred p]
    (S : Submodule K U) (m : ℕ)
    (hnew : ∀ i < m, a i ∉ prefixSpan (K := K) a i)
    (hgood : ∀ i < m, ¬p i → a i ∈ S ⊔ prefixSpan (K := K) a i) :
    m ≤ Module.finrank K S + ((range m).filter p).card := by
  calc
    _ = Module.finrank K (prefixSpan (K := K) a m) := (prefix_dimension a m hnew).symm
    _ ≤ Module.finrank K (S ⊔ failedSpan (K := K) a p m : Submodule K U) :=
      Submodule.finrank_mono (prefix_le_selected_and_failed a p S m hgood)
    _ ≤ Module.finrank K S + Module.finrank K (failedSpan (K := K) a p m) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := Nat.add_le_add_left (failed_dimension_le a p m) _

end PaperP1.SequentialRankBudget
