module

public import PaperP1.Coding.ComponentParityCode

/-! # A finite Runge--Hamming bound for small disjoint value components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallComponentBound

open Finset PaperP1.Arithmetic PaperP1.ComponentParityCode

theorem minimum_weight {m r K U R t : ℕ} (smallPrime : Fin r → ℕ)
    (blocks : Fin m → Finset ℕ) (hblocks : ∀ i, (blocks i).Nonempty)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (hsize : ∀ i, (blocks i).card ≤ K)
    (houtside : ∀ i p, (¬∃ j : Fin r, smallPrime j = p) → ∑ n ∈ blocks i, parityVec n p = 0)
    (hlower : ∀ i n, n ∈ blocks i → U ≤ n) (hupper : ∀ i n, n ∈ blocks i → n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) :
    HammingBound.MinWeightAbove (LinearMap.ker (parityMap smallPrime blocks)) (2 * t) := by
  intro c hc
  let x : Fin m → F₂ := c.val
  have hx0 : x ≠ 0 := fun h ↦ hc (Subtype.ext h)
  have hx : x ∈ LinearMap.ker (parityMap smallPrime blocks) := c.property
  have hne := selected_nonempty blocks hblocks x hx0
  have heven := kernel_even smallPrime blocks hdisj x hx
  have hsquare := kernel_square smallPrime blocks hdisj
    (fun i n hn ↦ by have := hlower i n hn; omega) houtside x hx
  have hcard := EvenSquareSelection.cardinal_gt hne heven hsquare
    (fun n hn ↦ by obtain ⟨i, _, hni⟩ := mem_biUnion.mp hn; exact hlower i n hni)
    (fun n hn ↦ by obtain ⟨i, _, hni⟩ := mem_biUnion.mp hn; exact hupper i n hni)
    hR hU hgrowth
  have hsize' := selected_card_le blocks hsize x
  by_contra hnot
  have hweight : hammingNorm x ≤ 2 * t := Nat.le_of_not_gt hnot
  have hmul := Nat.mul_le_mul_left K hweight
  nlinarith

theorem codimension_bound {m r : ℕ} (smallPrime : Fin r → ℕ) (blocks : Fin m → Finset ℕ) :
    m - (r + 1) ≤ Module.finrank F₂ (LinearMap.ker (parityMap smallPrime blocks)) :=
  DefectCodeRank.columns_sub_rows_le_finrank_ker (parityMap smallPrime blocks)

theorem volume_bound {m r K U R t : ℕ} (smallPrime : Fin r → ℕ)
    (blocks : Fin m → Finset ℕ) (hblocks : ∀ i, (blocks i).Nonempty)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (hsize : ∀ i, (blocks i).card ≤ K)
    (houtside : ∀ i p, (¬∃ j : Fin r, smallPrime j = p) → ∑ n ∈ blocks i, parityVec n p = 0)
    (hlower : ∀ i n, n ∈ blocks i → U ≤ n) (hupper : ∀ i n, n ∈ blocks i → n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U)
    (hrows : r + 1 ≤ m) :
    (∑ j ∈ range (t + 1), m.choose j) ≤ 2 ^ (r + 1) := by
  exact HammingBound.sum_choose_le_pow_of_finrank_ge
    (minimum_weight smallPrime blocks hblocks hdisj hsize houtside hlower hupper hR hU hgrowth)
    (codimension_bound smallPrime blocks) hrows

theorem finite_count {m r K U R t : ℕ} (smallPrime : Fin r → ℕ)
    (blocks : Fin m → Finset ℕ) (hblocks : ∀ i, (blocks i).Nonempty)
    (hdisj : Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j))) (hsize : ∀ i, (blocks i).card ≤ K)
    (houtside : ∀ i p, (¬∃ j : Fin r, smallPrime j = p) → ∑ n ∈ blocks i, parityVec n p = 0)
    (hlower : ∀ i n, n ∈ blocks i → U ≤ n) (hupper : ∀ i n, n ∈ blocks i → n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    m < max (r + 1) (2 * t * 2 ^ ((r + 1) / t + 1)) := by
  by_cases hrows : r + 1 ≤ m
  · by_cases htm : 2 * t ≤ m
    · exact (HammingDefectBound.length_lt_of_sum_choose_le_two_pow ht htm
        (volume_bound smallPrime blocks hblocks hdisj hsize houtside hlower hupper hR hU hgrowth hrows)).trans_le
        (le_max_right _ _)
    · have hm : m < 2 * t := by omega
      have hpow : 0 < 2 ^ ((r + 1) / t + 1) := by positivity
      exact (hm.trans_le (Nat.le_mul_of_pos_right _ hpow)).trans_le (le_max_right _ _)
  · exact (show m < r + 1 by omega).trans_le (le_max_left _ _)

end PaperP1.SmallComponentBound
