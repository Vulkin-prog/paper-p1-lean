module

public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.MissingBlockProbabilities
public import PaperP1.Model.RegularSetFinite

/-! # Companion T22.2: summing the missing-block inequality

The ordered lists are actual embeddings, so repeated sites are excluded by
construction. No separation, compatibility or cardinality cutoff is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MissingBlockTupleSum

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Probability RegularStarts MissingBlockProbabilities FactorialCountMoments Finset

local instance missingBlockTuplePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem sum_omitted_tuple_moments {G : Finset ℕ} {r L : ℕ}
    (t : OrderedTuple G (r + 1)) :
    (∑ x ∈ tupleValues t, infiniteJointMoment L ((tupleValues t).erase x)) =
      ∑ i : Fin (r + 1), infiniteJointMoment L (tupleValues (eraseTuple t i)) := by
  rw [sum_tupleValues]
  apply sum_congr rfl
  intro i _
  rw [tupleValues_erase]

theorem sum_missing_block_tuples_heterogeneous {N L : ℕ} (hL : 0 < L)
    (G : Finset ℕ) (hG : G ⊆ dyadicBlock N) (pmax : ℝ) (hpmax : 0 ≤ pmax)
    (hbound : ∀ x ∈ G, infiniteMarginal x L ≤ pmax) (r : ℕ)
    (A : Finset (OrderedTuple G (r + 1)))
    (hmiss : ∀ t ∈ A,
      ¬∃ w, IsFullSupportRelation (fun x : tupleValues t ↦ squareClassSpace x.val L) w) :
    (∑ t ∈ A, infiniteJointMoment L (tupleValues t)) ≤
      (r + 1 : ℕ) * (G.card : ℝ) * pmax * factorialCountMoment G L r := by
  classical
  calc
    _ ≤ ∑ t ∈ A, pmax *
        ∑ x ∈ tupleValues t, infiniteJointMoment L ((tupleValues t).erase x) := by
      apply sum_le_sum
      intro t ht
      exact joint_missing_block_bound_of_marginal_le L _ hL (hmiss t ht) pmax
        (fun x hx ↦ hbound x (tupleValues_subset t hx))
    _ = pmax *
        ∑ i : Fin (r + 1), ∑ t ∈ A, infiniteJointMoment L (tupleValues (eraseTuple t i)) := by
      simp_rw [sum_omitted_tuple_moments]
      rw [← mul_sum, sum_comm]
    _ ≤ pmax *
        ∑ _i : Fin (r + 1), (G.card : ℝ) *
          ∑ s : OrderedTuple G r, infiniteJointMoment L (tupleValues s) := by
      apply mul_le_mul_of_nonneg_left _ hpmax
      apply sum_le_sum
      intro i _
      exact sum_erased_tuple_bound (infiniteJointMoment L) (infiniteJointMoment_nonneg L) A i
    _ = _ := by
      rw [sum_tuple_joint_moments hG]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem sum_missing_block_tuples_card {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (G : Finset ℕ) (hG : G ⊆ regularStarts N L) (r : ℕ)
    (A : Finset (OrderedTuple G (r + 1)))
    (hmiss : ∀ t ∈ A,
      ¬∃ w, IsFullSupportRelation (fun x : tupleValues t ↦ squareClassSpace x.val L) w) :
    (∑ t ∈ A, infiniteJointMoment L (tupleValues t)) ≤
      (r + 1 : ℕ) * (G.card : ℝ) * (2 ^ L : ℝ)⁻¹ * factorialCountMoment G L r := by
  apply sum_missing_block_tuples_heterogeneous hL G (hG.trans (regularStarts_subset N L))
    (2 ^ L : ℝ)⁻¹ (by positivity) _ r A hmiss
  intro x hx
  have hxpos : 0 < x := by
    have := (mem_Ico.mp ((regularStarts_subset N L) (hG hx))).1
    omega
  exact (marginal_on_regular hxpos hL (hG hx)).le

/-- Literal rNp E(Z_G)_(r-1) conclusion, with tuple order written r+1.
The preceding theorem keeps the sharper factor |G| in place of N. -/
theorem companion_T22_2_sum {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (r : ℕ)
    (A : Finset (OrderedTuple (regularStarts N L) (r + 1)))
    (hmiss : ∀ t ∈ A,
      ¬∃ w, IsFullSupportRelation (fun x : tupleValues t ↦ squareClassSpace x.val L) w) :
    (∑ t ∈ A, infiniteJointMoment L (tupleValues t)) ≤
      (r + 1 : ℕ) * (N : ℝ) * (2 ^ L : ℝ)⁻¹ * factorialCountMoment (regularStarts N L) L r := by
  have hcard : ((regularStarts N L).card : ℝ) ≤ N := by
    have h := (card_le_card (regularStarts_subset N L)).trans_eq
      (RegularSetFinite.card_dyadicBlock N)
    exact_mod_cast h
  have h := sum_missing_block_tuples_card hN hL (regularStarts N L) (subset_refl _) r A hmiss
  apply h.trans
  apply mul_le_mul_of_nonneg_right _
    (factorialCountMoment_nonneg (regularStarts_subset N L) r)
  apply mul_le_mul_of_nonneg_right _ (show 0 ≤ (2 ^ L : ℝ)⁻¹ by positivity)
  exact mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg (r + 1))

end PaperP1.MissingBlockTupleSum
