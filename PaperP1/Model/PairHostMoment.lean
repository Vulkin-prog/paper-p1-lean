module

public import PaperP1.Arithmetic.PairHostCover
public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.TripleProbabilityBound
public import Mathlib.Tactic.FinCases

/-! # The actual second factorial moment splits into direct pairs and full-loss hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairHostMoment

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Affine PaperP1.Probability PaperP1.FactorialCountMoments
  PaperP1.NormalizedPairRankLoss

local instance pairHostMomentTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem zero_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hloss : pairLoss x y L = 0) :
    Module.finrank F₂ (squareClassSpace x L) = L ∧
      Module.finrank F₂ (squareClassSpace y L) = L ∧
      Disjoint (squareClassSpace x L) (squareClassSpace y L) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  have hrx := LocalRunRank.squareClass_rank_le x L hx
  have hry := LocalRunRank.squareClass_rank_le y L hy
  unfold pairLoss at hloss
  have hinf : Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) = 0 := by omega
  exact ⟨by omega, by omega, disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)⟩

def tuplePair {G : Finset ℕ} (t : OrderedTuple G 2) : ℕ × ℕ := ((t 0).val, (t 1).val)

theorem tuplePair_injective (G : Finset ℕ) : Function.Injective (tuplePair (G := G)) := by
  intro t u h
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem tupleValues_pair {G : Finset ℕ} (t : OrderedTuple G 2) :
    tupleValues t = {(t 0).val, (t 1).val} := by
  ext x
  rw [mem_tupleValues]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact mem_insert.mpr (Or.inl hi.symm)
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr hi.symm))
  · intro hx
    rcases mem_insert.mp hx with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, (mem_singleton.mp hx).symm⟩

def badTuples (N L : ℕ) : Finset (OrderedTuple (dyadicBlock N) 2) :=
  univ.filter fun t ↦ 0 < pairLoss (t 0).val (t 1).val L

theorem badTuples_card (N L : ℕ) : (badTuples N L).card ≤ (PairHostCover.hosts N L).card := by
  apply card_le_card_of_injOn tuplePair
  · intro t ht
    exact mem_filter.mpr ⟨mem_product.mpr ⟨(t 0).property, (t 1).property⟩, (mem_filter.mp ht).2⟩
  · exact (tuplePair_injective _).injOn

theorem finite_second_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) {M : ℝ} (hM : 0 ≤ M)
    (hmarg : ∀ x ∈ dyadicBlock N, infiniteMarginal x L ≤ M) :
    factorialCountMoment (dyadicBlock N) L 2 ≤
      (N : ℝ) ^ 2 * (((2 ^ L : ℝ)⁻¹) ^ 2) + (PairHostCover.hosts N L).card * M := by
  classical
  have htuple : ∀ t : OrderedTuple (dyadicBlock N) 2,
      infiniteJointMoment L (tupleValues t) ≤
        (((2 ^ L : ℝ)⁻¹) ^ 2) + if t ∈ badTuples N L then M else 0 := by
    intro t
    have hxpos : 0 < (t 0).val := by have h := (mem_Ico.mp (t 0).property).1; omega
    have hypos : 0 < (t 1).val := by have h := (mem_Ico.mp (t 1).property).1; omega
    have hxy : (t 0).val ≠ (t 1).val := by
      intro h
      have hi := t.injective (Subtype.ext h)
      norm_num at hi
    by_cases ht : t ∈ badTuples N L
    · rw [ite_eq_left ht]
      have hmono : infiniteJointMoment L (tupleValues t) ≤ infiniteMarginal (t 0).val L := by
        calc
          _ ≤ infiniteJointMoment L {(t 0).val} := infiniteJointMoment_antitone L (by
            intro x hx
            rw [mem_singleton.mp hx]
            exact (mem_tupleValues t _).mpr ⟨0, rfl⟩)
          _ = _ := by simp only [infiniteJointMoment, prod_singleton, infiniteMarginal]
      exact (hmono.trans (hmarg _ (t 0).property)).trans (le_add_of_nonneg_left (sq_nonneg _))
    · rw [ite_eq_right ht, add_zero, tupleValues_pair]
      have hloss : pairLoss (t 0).val (t 1).val L = 0 := by
        have hnot : ¬0 < pairLoss (t 0).val (t 1).val L := by
          intro h
          exact ht (mem_filter.mpr ⟨mem_univ _, h⟩)
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
        ((((2 ^ L : ℝ)⁻¹) ^ 2) + if t ∈ badTuples N L then M else 0) :=
      sum_le_sum (fun t _ ↦ htuple t)
    _ = (Fintype.card (OrderedTuple (dyadicBlock N) 2) : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ 2) +
        (badTuples N L).card * M := by rw [sum_add_distrib, hbad]; simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
      (mul_le_mul_of_nonneg_right (by exact_mod_cast badTuples_card N L) hM)

end PaperP1.PairHostMoment
