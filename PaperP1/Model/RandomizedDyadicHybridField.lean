module

public import PaperP1.Model.RandomizedHybridField
public import PaperP1.Model.AnchoredDyadicField
public import PaperP1.Arithmetic.OrdinarySmoothSourcePopulation

/-! # The randomized hybrid on the literal original dyadic retained field

The strict full-good subset is defined by the actual maximal support.
Every allowed arithmetic anchor rule on the original at-most-one-small
population gives the hybrid data, with no conditional-law premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedDyadicHybridField

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.OddPrimePivot PaperP1.Probability PaperP1.AnchoredPrivateField

def fullGood (N B Z : ℕ) : Finset ℕ := boundaryBlock N \ badBoundaries N B Z

theorem mem_fullGood {N B Z j : ℕ} (hN : 2 ≤ N) :
    j ∈ fullGood N B Z ↔ j ∈ boundaryBlock N ∧
      ∀ i : Fin B, Z < largestOddPrime (j + i.val) := by
  constructor
  · intro hj
    obtain ⟨hj, hn⟩ := mem_sdiff.mp hj
    refine ⟨hj, fun i ↦ ?_⟩
    by_contra hi
    exact hn ((mem_badBoundaries hN).mpr ⟨hj, i, Nat.le_of_not_gt hi⟩)
  · rintro ⟨hj, hg⟩
    refine mem_sdiff.mpr ⟨hj, ?_⟩
    intro hb
    obtain ⟨_, i, hi⟩ := (mem_badBoundaries hN).mp hb
    exact (not_le_of_gt (hg i)) hi

theorem fullGood_subset_retained {N B Y Z : ℕ} (hN : 2 ≤ N) (hYZ : Y ≤ Z) :
    fullGood N B Z ⊆ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y := by
  intro j hj
  obtain ⟨hjB, hjbad⟩ := mem_sdiff.mp hj
  exact PaperP1.AnchoredDyadicField.retained_of_not_bad hN hYZ hjB hjbad

theorem fullGood_deletion_ledger {N B Z : ℕ} (hN : 2 ≤ N) :
    (fullGood N B Z).card + (badBoundaries N B Z).card = N := by
  have hs : badBoundaries N B Z ⊆ boundaryBlock N := fun _ hj ↦ ((mem_badBoundaries hN).mp hj).1
  simpa only [fullGood, boundaryBlock_card hN] using card_sdiff_add_card_eq_card hs

theorem ordinary_sources_subset (N K B Z : ℕ) (Q : ℝ) :
    PaperP1.OrdinarySmoothSourcePopulation.goodSources N K B Z Q ⊆ fullGood N B Z := by
  intro j hj
  obtain ⟨hjB, _, hjbad⟩ := PaperP1.OrdinarySmoothSourcePopulation.mem_goodSources.mp hj
  exact mem_sdiff.mpr ⟨hjB, hjbad⟩

theorem data {N B Y Z K M : ℕ} (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hBY : B ≤ Y)
    (hYZ : Y ≤ Z) (hM : 2 * N + B ≤ M)
    (anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1))
    (hrule : ∀ j : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y, ∀ i : Fin (K + 1),
      largestOddPrime (j.val + i.val) ≤ Y → i = anchor j) :
    PaperP1.RandomizedHybridField.Data M Y K
      (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) (fullGood N B Z) anchor := {
  anchored := PaperP1.AnchoredDyadicField.data hN hKB hBY hM anchor hrule
  good := by
    intro j hj i
    have hg := (mem_fullGood hN).mp hj
    exact hYZ.trans_lt (hg.2 (Fin.castLE hKB i))
  }

theorem total_mean_upper {N B Y Z K M : ℕ} {Ξ : Type*} [Fintype Ξ]
    {anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1)}
    (D : PaperP1.RandomizedHybridField.Data M Y K
      (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y) (fullGood N B Z) anchor)
    (P : FiniteProbability Ξ) (b : Fin (K + 1) → F₂) :
    (∑ j : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y,
      exactMarginal (PaperP1.RandomizedHybridField.law (M := M) P)
        (PaperP1.RandomizedHybridField.indicator b) j) ≤ (N : ℝ) * rate K := by
  simp only [PaperP1.RandomizedHybridField.indicator_marginal D, sum_const, card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast PaperP1.AnchoredDyadicField.retained_card_le N B Y) (rate_pos K).le

end PaperP1.RandomizedDyadicHybridField
