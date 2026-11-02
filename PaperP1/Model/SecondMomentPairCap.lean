module

public import PaperP1.Model.PairHostMoment

/-! # The actual second factorial moment from a joint cap on distinct full-loss pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondMomentPairCap

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic
  PaperP1.Probability PaperP1.FactorialCountMoments PaperP1.PairHostMoment PaperP1.NormalizedPairRankLoss

theorem finite_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {M : ℝ} (hM : 0 ≤ M)
    (hpair : ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N, x ≠ y →
      infiniteJointMoment L {x, y} ≤ M) :
    factorialCountMoment (dyadicBlock N) L 2 ≤
      (N : ℝ) ^ 2 * (((2 ^ L : ℝ)⁻¹) ^ 2) + (PairHostCover.hosts N L).card * M := by
  classical
  have htuple (t : OrderedTuple (dyadicBlock N) 2) :
      infiniteJointMoment L (tupleValues t) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 +
        if t ∈ badTuples N L then M else 0 := by
    have hxpos : 0 < (t 0).val := by have h := (mem_Ico.mp (t 0).property).1; omega
    have hypos : 0 < (t 1).val := by have h := (mem_Ico.mp (t 1).property).1; omega
    have hxy : (t 0).val ≠ (t 1).val := by
      intro h
      have hi := t.injective (Subtype.ext h)
      norm_num at hi
    by_cases ht : t ∈ badTuples N L
    · rw [ite_eq_left ht, tupleValues_pair]
      exact (hpair _ (t 0).property _ (t 1).property hxy).trans (le_add_of_nonneg_left (sq_nonneg _))
    · rw [ite_eq_right ht, add_zero, tupleValues_pair]
      have hloss : pairLoss (t 0).val (t 1).val L = 0 := by
        have hn : ¬ 0 < pairLoss (t 0).val (t 1).val L :=
          fun h ↦ ht (mem_filter.mpr ⟨mem_univ _, h⟩)
        omega
      obtain ⟨hx, hy, hdirect⟩ := zero_loss hxpos hypos hloss
      exact TripleProbabilityBound.pair_joint_le hxy hxpos hypos hL hx hy hdirect
  have hbad : (∑ t : OrderedTuple (dyadicBlock N) 2, if t ∈ badTuples N L then M else 0) =
      (badTuples N L).card * M := by
    rw [← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (OrderedTuple (dyadicBlock N) 2) : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, dyadicBlock_card]
    exact_mod_cast Nat.descFactorial_le_pow N 2
  rw [← sum_tuple_joint_moments (subset_refl _) 2]
  calc
    _ ≤ ∑ t : OrderedTuple (dyadicBlock N) 2,
        (((2 ^ L : ℝ)⁻¹) ^ 2 + if t ∈ badTuples N L then M else 0) := sum_le_sum (fun t _ht ↦ htuple t)
    _ = (Fintype.card (OrderedTuple (dyadicBlock N) 2) : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ 2) +
        (badTuples N L).card * M := by rw [sum_add_distrib, hbad]; simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast badTuples_card N L) hM)

end PaperP1.SecondMomentPairCap
