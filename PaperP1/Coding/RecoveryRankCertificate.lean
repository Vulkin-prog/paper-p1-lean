module

public import PaperP1.Coding.SequentialRankBudget
public import PaperP1.Coding.RecoverySampling
public import Mathlib.Tactic.Push

/-! # Discharging the deterministic premise of the recovery sampling bound

Recorded recoveries modulo earlier independent directions give the actual
pointwise rank inequality. Existence and maximality of such a history, and
the final independent-representation count, are still separate obligations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RecoveryRankCertificate

open Finset Submodule PaperP1.SequentialRankBudget PaperP1.FiniteBernoulliSubset

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [Fintype V] [DecidableEq V]

local instance recoveryCertificateDecidableEq : DecidableEq U := Classical.decEq _

def selectionSpan (L : V → U) (σ : V → Bool) : Submodule K U :=
  span K (↑((selected σ).image L) : Set U)

omit [FiniteDimensional K U] [DecidableEq V] in
theorem selectionSpan_dimension_le (L : V → U) (σ : V → Bool) :
    Module.finrank K (selectionSpan (K := K) L σ) ≤ (selected σ).card := by
  exact (finrank_span_finset_le_card ((selected σ).image L)).trans card_image_le

omit [DecidableEq V] in
theorem pointwise_rank_certificate (L : V → U) (a : ℕ → U) (m t : ℕ)
    (A : ℕ → Fin t → Finset V)
    (hnew : ∀ i < m, a i ∉ prefixSpan (K := K) a i)
    (hrecovery : ∀ i < m, ∀ j : Fin t,
      a i - (∑ v ∈ A i j, L v) ∈ prefixSpan (K := K) a i) :
    ∀ σ : V → Bool, (m : ℝ) ≤ ((selected σ).card : ℝ) + RecoverySampling.failureCount m t A σ := by
  classical
  intro σ
  let p : ℕ → Prop := fun i ↦ ∀ j : Fin t, ¬ A i j ⊆ selected σ
  have hgood : ∀ i < m, ¬p i → a i ∈ selectionSpan (K := K) L σ ⊔ prefixSpan a i := by
    intro i hi hnot
    change ¬(∀ j : Fin t, ¬A i j ⊆ selected σ) at hnot
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hsum : (∑ v ∈ A i j, L v) ∈ selectionSpan (K := K) L σ := by
      apply Submodule.sum_mem
      intro v hv
      exact subset_span (mem_image.mpr ⟨v, hj hv, rfl⟩)
    apply Submodule.mem_sup.mpr
    refine ⟨∑ v ∈ A i j, L v, hsum, a i - (∑ v ∈ A i j, L v), hrecovery i hi j, ?_⟩
    rw [add_comm, sub_add_cancel]
  have hnat : m ≤ (selected σ).card + ((range m).filter p).card :=
    (rank_budget a p (selectionSpan (K := K) L σ) m hnew hgood).trans
      (Nat.add_le_add_right (selectionSpan_dimension_le L σ) _)
  have hfail : (((range m).filter p).card : ℝ) = RecoverySampling.failureCount m t A σ := by
    unfold RecoverySampling.failureCount
    rw [card_eq_sum_ones, sum_filter, Nat.cast_sum]
    apply sum_congr rfl
    intro i _
    rw [failure_eq_indicator]
    simp
  have hreal : (m : ℝ) ≤ ((selected σ).card : ℝ) + (((range m).filter p).card : ℝ) := by
    exact_mod_cast hnat
  rwa [hfail] at hreal

theorem recorded_history_cost_bound (L : V → U) (a : ℕ → U) (m d t : ℕ)
    (hd : 1 ≤ d) (ht : 2 ≤ t) (A : ℕ → Fin t → Finset V)
    (hnew : ∀ i < m, a i ∉ prefixSpan (K := K) a i)
    (hrecovery : ∀ i < m, ∀ j : Fin t,
      a i - (∑ v ∈ A i j, L v) ∈ prefixSpan (K := K) a i)
    (hdisj : ∀ i < m, (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint (A i))
    (hcard : ∀ i < m, ∀ j, (A i j).card ≤ d) :
    (m : ℝ) ≤ 2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t :=
  RecoverySampling.sampling_cost_bound m d t hd ht A hdisj hcard
    (pointwise_rank_certificate L a m t A hnew hrecovery)

end PaperP1.RecoveryRankCertificate
