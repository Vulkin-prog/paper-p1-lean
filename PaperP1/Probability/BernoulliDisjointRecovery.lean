module

public import PaperP1.Probability.FiniteBernoulliSubset

/-! # The exact failure probability for disjoint recovery sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteBernoulliSubset

open Finset PaperP1.Algebra

variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]

def failure (G : Finset J) (A : J → Finset V) (σ : V → Bool) : ℝ :=
  ∏ j ∈ G, (1 - allTrue (A j) σ)

theorem allTrue_eq_subset_indicator (A : Finset V) (σ : V → Bool) :
    allTrue A σ = if A ⊆ selected σ then 1 else 0 := by
  classical
  have hcond : A ⊆ selected σ ↔ ∀ v ∈ A, σ v = true := by
    simp only [Finset.subset_iff, selected, mem_filter, mem_univ, true_and]
  simp only [allTrue_eq_indicator, hcond]

theorem failure_eq_indicator (G : Finset J) (A : J → Finset V) (σ : V → Bool) :
    failure G A σ = if (∀ j ∈ G, ¬ A j ⊆ selected σ) then 1 else 0 := by
  classical
  induction G using Finset.induction_on with
  | empty => simp [failure]
  | @insert j G hj ih =>
    rw [failure, prod_insert hj, ← failure, ih, allTrue_eq_subset_indicator]
    by_cases h : A j ⊆ selected σ <;> simp [h]

omit [DecidableEq J] in
theorem expectation_joint_recovery (u : ℝ) (G : Finset J) (A : J → Finset V)
    (hdisj : (↑G : Set J).PairwiseDisjoint A) :
    finiteExpectation (weight u) (fun σ : V → Bool ↦ ∏ j ∈ G, allTrue (A j) σ) =
      ∏ j ∈ G, u ^ (A j).card := by
  have hpoint : (fun σ : V → Bool ↦ ∏ j ∈ G, allTrue (A j) σ) = allTrue (G.biUnion A) := by
    funext σ
    simp only [allTrue]
    rw [prod_biUnion hdisj]
  rw [hpoint, expectation_allTrue, card_biUnion hdisj, prod_pow_eq_pow_sum]

theorem expectation_failure_exact (u : ℝ) (G : Finset J) (A : J → Finset V)
    (hdisj : (↑G : Set J).PairwiseDisjoint A) :
    finiteExpectation (weight u) (failure G A) = ∏ j ∈ G, (1 - u ^ (A j).card) := by
  have hpoint (σ : V → Bool) : failure G A σ =
      ∑ I ∈ G.powerset, (-1 : ℝ) ^ I.card * ∏ j ∈ I, allTrue (A j) σ := by
    simpa only [failure, prod_const_one, mul_one] using prod_sub
      (fun _ : J ↦ (1 : ℝ)) (fun j ↦ allTrue (A j) σ) G
  have hE := finiteExpectation_sum (weight u) G.powerset
    (fun (I : Finset J) (σ : V → Bool) ↦ (-1 : ℝ) ^ I.card * ∏ j ∈ I, allTrue (A j) σ)
  calc
    _ = finiteExpectation (weight u) (fun σ : V → Bool ↦
        ∑ I ∈ G.powerset, (-1 : ℝ) ^ I.card * ∏ j ∈ I, allTrue (A j) σ) := by
      congr 1
      funext σ
      exact hpoint σ
    _ = ∑ I ∈ G.powerset, (-1 : ℝ) ^ I.card *
        finiteExpectation (weight u) (fun σ : V → Bool ↦ ∏ j ∈ I, allTrue (A j) σ) := by
      rw [hE]
      apply sum_congr rfl
      intro I _
      exact finiteExpectation_const_mul _ _ _
    _ = ∑ I ∈ G.powerset, (-1 : ℝ) ^ I.card * ∏ j ∈ I, u ^ (A j).card := by
      apply sum_congr rfl
      intro I hI
      have hsub : (↑I : Set J) ⊆ ↑G := mem_powerset.mp hI
      rw [expectation_joint_recovery u I A (Set.Pairwise.mono hsub hdisj)]
    _ = _ := by
      simpa only [prod_const_one, mul_one] using (prod_sub
        (fun _ : J ↦ (1 : ℝ)) (fun j ↦ u ^ (A j).card) G).symm

theorem expectation_failure_le (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (G : Finset J) (A : J → Finset V) (hdisj : (↑G : Set J).PairwiseDisjoint A)
    (d : ℕ) (hcard : ∀ j ∈ G, (A j).card ≤ d) :
    finiteExpectation (weight u) (failure G A) ≤ (1 - u ^ d) ^ G.card := by
  rw [expectation_failure_exact u G A hdisj, ← prod_const]
  apply prod_le_prod₀
  · intro j _
    exact sub_nonneg.mpr (pow_le_one₀ hu0 hu1)
  · intro j hj
    exact sub_le_sub_left (pow_le_pow_of_le_one hu0 hu1 (hcard j hj)) 1

end PaperP1.FiniteBernoulliSubset
