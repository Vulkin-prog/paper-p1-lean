module

public import PaperP1.Probability.BernoulliDisjointRecovery
public import PaperP1.Probability.FiniteCoupling
public import PaperP1.Analysis.DisjointRecoveryParameters
public import Mathlib.Tactic.Linarith

/-! # The probabilistic cost of a recorded disjoint-recovery history

The deterministic rank certificate is an explicit premise of the last lemma.
Constructing that certificate and the stopping space are separate obligations;
this module alone does not prove article Lemma 6.1.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RecoverySampling

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.FiniteBernoulliSubset
open PaperP1.DisjointRecoveryParameters

variable {V : Type*} [Fintype V] [DecidableEq V]

def failureCount (m t : ℕ) (A : ℕ → Fin t → Finset V) (σ : V → Bool) : ℝ :=
  ∑ i ∈ range m, failure univ (A i) σ

theorem expectation_one_failure_le_half (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t)
    (A : Fin t → Finset V) (hdisj : (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint A)
    (hcard : ∀ j, (A j).card ≤ d) :
    finiteExpectation (weight (parameter d t)) (failure univ A) ≤ (1 : ℝ) / 2 := by
  have h := expectation_failure_le (parameter d t) (parameter_pos d t ht).le
    (parameter_lt_one d t hd ht).le univ A hdisj d (fun j _ ↦ hcard j)
  rw [card_univ, Fintype.card_fin] at h
  exact h.trans (failure_factor_le_half d t hd ht)

theorem expectation_failureCount_le (m d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t)
    (A : ℕ → Fin t → Finset V)
    (hdisj : ∀ i < m, (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint (A i))
    (hcard : ∀ i < m, ∀ j, (A i j).card ≤ d) :
    finiteExpectation (weight (parameter d t)) (failureCount m t A) ≤ (m : ℝ) / 2 := by
  unfold failureCount
  rw [finiteExpectation_sum]
  calc
    _ ≤ ∑ _i ∈ range m, (1 : ℝ) / 2 := by
      apply sum_le_sum
      intro i hi
      exact expectation_one_failure_le_half d t hd ht (A i) (hdisj i (mem_range.mp hi))
        (hcard i (mem_range.mp hi))
    _ = _ := by simp [div_eq_mul_inv]

/-- The sampling step, conditional only on its displayed deterministic rank
certificate. This is not counted as the manuscript's subspace theorem. -/
theorem sampling_cost_bound (m d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t)
    (A : ℕ → Fin t → Finset V)
    (hdisj : ∀ i < m, (↑(univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint (A i))
    (hcard : ∀ i < m, ∀ j, (A i j).card ≤ d)
    (hcost : ∀ σ : V → Bool, (m : ℝ) ≤ ((selected σ).card : ℝ) + failureCount m t A σ) :
    (m : ℝ) ≤ 2 * (Fintype.card V : ℝ) * parameter d t := by
  let P := probability (V := V) (parameter d t) (parameter_pos d t ht).le
    (parameter_lt_one d t hd ht).le
  have h := finiteExpectation_mono P hcost
  change finiteExpectation (weight (parameter d t)) (fun _ : V → Bool ↦ (m : ℝ)) ≤
    finiteExpectation (weight (parameter d t))
      (fun σ : V → Bool ↦ ((selected σ).card : ℝ) + failureCount m t A σ) at h
  rw [finiteExpectation_const, weight_total, one_mul, finiteExpectation_add,
    expectation_selected_card] at h
  have hfail := expectation_failureCount_le m d t hd ht A hdisj hcard
  nlinarith

end PaperP1.RecoverySampling
