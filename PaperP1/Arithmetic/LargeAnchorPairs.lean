module

public import PaperP1.Arithmetic.SelectedKernelWitness
public import PaperP1.Arithmetic.WeightedKernelTail

/-! # Counting actual anchored square-parity relations in two dyadic windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeAnchorPairs

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.LargeOddKernel
open PaperP1.KernelSupportFibres PaperP1.KernelAssignments PaperP1.SelectedKernelWitness
open PaperP1.TruncatedKernelProducts PaperP1.WeightedKernelTail

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def leftPairs (N B : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico N (2 * N)) ×ˢ (Finset.Ico N (2 * N))).filter fun xy ↦
    ∃ i : Fin B, T < (largeOddKernel B (xy.1 - 1 + i.val) : ℝ) ∧
      AnchoredRelation (xy.1 - 1) (xy.2 - 1) B i

def bothPairs (N B : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  leftPairs N B T ∪ (leftPairs N B T).image Prod.swap

def anchoredHosts (N B n : ℕ) (i : Fin B) : Finset (ℕ × ℕ) :=
  (hits (roughSupport B n) B N N).image fun y ↦ (n + 1 - i.val, y)

theorem left_pairs_cover {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    leftPairs N B T ⊆ (univ : Finset (Fin B)).biUnion fun i ↦
      (Finset.Icc 1 (3 * N)).biUnion fun n ↦
        if T < (largeOddKernel B n : ℝ) then anchoredHosts N B n i else ∅ := by
  intro xy hxy
  obtain ⟨hxy, i, hT, hrel⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  let n := xy.1 - 1 + i.val
  have hi := i.isLt
  have hn : n ∈ Finset.Icc 1 (3 * N) := mem_Icc.mpr ⟨by dsimp [n]; omega, by dsimp [n]; omega⟩
  have hyhit : xy.2 ∈ hits (roughSupport B n) B N N :=
    other_start_mem_hits i (by simpa only [two_mul] using hy) hrel
  have hxrec : n + 1 - i.val = xy.1 := by dsimp [n]; omega
  refine mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨n, hn, ?_⟩⟩
  rw [ite_eq_left hT]
  exact mem_image.mpr ⟨xy.2, hyhit, Prod.ext hxrec rfl⟩

theorem left_pairs_card_sum {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    (leftPairs N B T).card ≤ B *
      ∑ n ∈ Finset.Icc 1 (3 * N),
        if T < (largeOddKernel B n : ℝ) then (hits (roughSupport B n) B N N).card else 0 := by
  calc
    _ ≤ ((univ : Finset (Fin B)).biUnion fun i ↦
        (Finset.Icc 1 (3 * N)).biUnion fun n ↦
          if T < (largeOddKernel B n : ℝ) then anchoredHosts N B n i else ∅).card :=
      card_le_card (left_pairs_cover T hN hB)
    _ ≤ ∑ i : Fin B, ((Finset.Icc 1 (3 * N)).biUnion fun n ↦
        if T < (largeOddKernel B n : ℝ) then anchoredHosts N B n i else ∅).card := card_biUnion_le
    _ ≤ ∑ i : Fin B, ∑ n ∈ Finset.Icc 1 (3 * N),
        (if T < (largeOddKernel B n : ℝ) then anchoredHosts N B n i else ∅).card :=
      sum_le_sum (fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ _i : Fin B, ∑ n ∈ Finset.Icc 1 (3 * N),
        if T < (largeOddKernel B n : ℝ) then (hits (roughSupport B n) B N N).card else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro n _
      split_ifs
      · exact card_image_le
      · exact le_rfl
    _ = _ := by simp

theorem kernel_le_anchor {B n : ℕ} (hn : 0 < n) : largeOddKernel B n ≤ n := by
  have heq := PaperP1.RankinSmallKernel.truncatedKernel_eq_floor (B : ℝ) (Nat.cast_nonneg B) n
  rw [Nat.floor_natCast] at heq
  rw [← heq]
  exact kernel_le B n hn

theorem left_pairs_weighted {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    ((leftPairs N B T).card : ℝ) ≤ 4 * B * N * weightedTail B (3 * N) T := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 (3 * N)) :
      ((if T < (largeOddKernel B n : ℝ) then (hits (roughSupport B n) B N N).card else 0 : ℕ) : ℝ) ≤
        4 * N * supportTail B T (roughSupport B n) := by
    by_cases hT : T < (largeOddKernel B n : ℝ)
    · rw [ite_eq_left hT, supportTail, support_product, ite_eq_left hT]
      have h := hits_card_real (roughSupport B n) B N N
        (fun p hp ↦ prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1) (by omega)
        ((kernel_le_anchor (mem_Icc.mp hn).1).trans (mem_Icc.mp hn).2)
      rw [support_product] at h
      convert h using 1; ring
    · unfold supportTail
      rw [support_product, ite_eq_right hT, ite_eq_right hT, Nat.cast_zero, mul_zero]
  calc
    _ ≤ (B : ℝ) * ∑ n ∈ Finset.Icc 1 (3 * N),
        ((if T < (largeOddKernel B n : ℝ) then (hits (roughSupport B n) B N N).card else 0 : ℕ) : ℝ) := by
      exact_mod_cast left_pairs_card_sum T hN hB
    _ ≤ (B : ℝ) * ∑ n ∈ Finset.Icc 1 (3 * N), 4 * N * supportTail B T (roughSupport B n) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg B)
    _ = _ := by rw [← mul_sum]; unfold weightedTail; ring

theorem both_pairs_weighted {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    ((bothPairs N B T).card : ℝ) ≤ 8 * B * N * weightedTail B (3 * N) T := by
  have hcard : (bothPairs N B T).card ≤ 2 * (leftPairs N B T).card := by
    calc
      _ ≤ (leftPairs N B T).card + ((leftPairs N B T).image Prod.swap).card := card_union_le _ _
      _ ≤ (leftPairs N B T).card + (leftPairs N B T).card := Nat.add_le_add_left card_image_le _
      _ = _ := by omega
  have hcast : ((bothPairs N B T).card : ℝ) ≤ 2 * ((leftPairs N B T).card : ℝ) := by exact_mod_cast hcard
  exact hcast.trans (by nlinarith [left_pairs_weighted T hN hB])

theorem finite_exp_bound {N B : ℕ} (T τ : ℝ) (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hT : 0 < T) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ((bothPairs N B T).card : ℝ) ≤
      8 * B * N * Real.sqrt (3 * N) * T ^ (-1 / 2 + τ) *
        Real.exp (2 * Real.sqrt B + PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
  have htail := weighted_tail_exp B (3 * N) T τ hB hT hτ hτhalf
  have hmul := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ 8 * B * N)
  refine (both_pairs_weighted T hN hBN).trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hmul

end PaperP1.LargeAnchorPairs
