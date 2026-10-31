module

public import PaperP1.Coding.DisjointRecoveryHistory
public import PaperP1.Coding.RecoveryRankCertificate
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fintype.EquivFin

/-! # A small-codimension subspace with no disjoint recovery system

The maximal history and its rank certificate are constructed internally.
The independent-label representation count from article 6.1 is separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointRecoverySubspace

open Finset Submodule PaperP1.SequentialRankBudget PaperP1.DisjointRecoveryHistory

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [Fintype V] [DecidableEq V]

local instance recoverySubspaceDualDecidableEq (M : Submodule K U) : DecidableEq (Module.Dual K M) :=
  Classical.decEq _

theorem exists_small_stopping_span (L : V → U) (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ W : Submodule K U,
      (Module.finrank K W : ℝ) ≤ 2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t ∧
      ¬ HasBadRecoveries L d t W := by
  obtain ⟨m, a, A, hhistory, hstop⟩ := exists_maximal_history (K := K) L d t
  have hcost := RecoveryRankCertificate.recorded_history_cost_bound L a m d t hd ht A
    (fun i hi ↦ (hhistory i hi).1) (fun i hi ↦ (hhistory i hi).2.2.2)
    (fun i hi ↦ (hhistory i hi).2.1) (fun i hi j ↦ ((hhistory i hi).2.2.1 j).2)
  refine ⟨prefixSpan (K := K) a m, ?_, hstop⟩
  rw [prefix_dimension a m (fun i hi ↦ (hhistory i hi).1)]
  exact hcost

def NoDisjointRecovery (L : V → Module.Dual K U) (M : Submodule K U) (d t : ℕ) : Prop :=
  ∀ α : Module.Dual K M, α ≠ 0 → ∀ A : Fin t → Finset V,
    (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint A →
    (∀ j : Fin t, 1 ≤ (A j).card ∧ (A j).card ≤ d) →
    (∀ j : Fin t, (∑ v ∈ A j, (L v).comp M.subtype) = α) → False

theorem exists_small_recovery_subspace (L : V → Module.Dual K U) (d t : ℕ)
    (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule K U,
      ((Module.finrank K U - Module.finrank K M : ℕ) : ℝ) ≤
        2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t ∧
      NoDisjointRecovery L M d t := by
  obtain ⟨W, hcost, hstop⟩ := exists_small_stopping_span (K := K) L d t hd ht
  let M := W.dualCoannihilator
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have hcodim : Module.finrank K U - Module.finrank K M = Module.finrank K W := by
    change Module.finrank K U - Module.finrank K W.dualCoannihilator = _
    omega
  have hker : LinearMap.ker M.dualRestrict = W := by
    rw [Submodule.dualRestrict_ker_eq_dualAnnihilator]
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  refine ⟨M, ?_, ?_⟩
  · rwa [hcodim]
  · intro α hα A hdisj hcard hrec
    obtain ⟨β, hβ⟩ := Subspace.dualRestrict_surjective (W := M) α
    have hβW : β ∉ W := by
      intro hβW
      have hβker : β ∈ LinearMap.ker M.dualRestrict := by rwa [hker]
      exact hα (hβ.symm.trans (LinearMap.mem_ker.mp hβker))
    apply hstop
    refine ⟨β, hβW, A, hdisj, hcard, ?_⟩
    intro j
    rw [← hker, LinearMap.mem_ker, map_sub, map_sum, hβ]
    change α - (∑ v ∈ A j, (L v).comp M.subtype) = 0
    rw [hrec j, sub_self]

omit [FiniteDimensional K U] [DecidableEq V] in
theorem coordinate_multiplicity_le (L : V → Module.Dual K U) (M : Submodule K U)
    (d t : ℕ) (hd : 1 ≤ d) (hno : NoDisjointRecovery L M d t)
    (α : Module.Dual K M) (hα : α ≠ 0) :
    ((univ.filter fun v ↦ (L v).comp M.subtype = α).card : ℕ) ≤ t - 1 := by
  classical
  let S := univ.filter fun v ↦ (L v).comp M.subtype = α
  by_contra hnot
  change ¬S.card ≤ t - 1 at hnot
  have htS : t ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := exists_subset_card_eq htS
  let e : Fin t ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let A : Fin t → Finset V := fun j ↦ {(e j).val}
  apply hno α hα A
  · intro j _ k _ hjk
    apply disjoint_left.mpr
    intro v hvj hvk
    have heq : (e j).val = (e k).val :=
      (mem_singleton.mp hvj).symm.trans (mem_singleton.mp hvk)
    exact hjk (e.injective (Subtype.ext heq))
  · intro j
    simpa only [A, card_singleton] using And.intro (le_refl 1) hd
  · intro j
    change (∑ v ∈ ({(e j).val} : Finset V), (L v).comp M.subtype) = α
    rw [sum_singleton]
    exact (mem_filter.mp (hTS (e j).property)).2

end PaperP1.DisjointRecoverySubspace
