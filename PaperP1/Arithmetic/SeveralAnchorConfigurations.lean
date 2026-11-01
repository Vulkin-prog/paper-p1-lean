module

public import PaperP1.Arithmetic.SeveralSelectedKernelWitness
public import PaperP1.Arithmetic.WeightedReceiverKernelTail
public import PaperP1.Arithmetic.LargeAnchorPairs

/-! # Actual anchored relations with an arbitrary finite family of receiver windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralAnchorConfigurations

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.LargeOddKernel
open PaperP1.KernelSupportFibres PaperP1.SeveralSelectedKernelWitness
open PaperP1.WeightedReceiverKernelTail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def configurations (N B : ℕ) (T : ℝ) : Finset (ℕ × (ι → ℕ)) :=
  ((Finset.Ico N (2 * N)) ×ˢ (Fintype.piFinset fun _ : ι ↦ Finset.Ico N (2 * N))).filter fun xz ↦
    ∃ i : Fin B, T < (largeOddKernel B (xz.1 - 1 + i.val) : ℝ) ∧
      AnchoredRelation (xz.1 - 1) (fun k ↦ xz.2 k - 1) B i

def anchorHosts (N B n : ℕ) (i : Fin B) : Finset (ℕ × (ι → ℕ)) :=
  (PaperP1.SeveralKernelReceivers.hits (ι := ι) (roughSupport B n) B N N).image
    fun z ↦ (n + 1 - i.val, z)

theorem configurations_cover {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    configurations (ι := ι) N B T ⊆ (univ : Finset (Fin B)).biUnion fun i ↦
      (Finset.Icc 1 (3 * N)).biUnion fun n ↦
        if T < (largeOddKernel B n : ℝ) then anchorHosts (ι := ι) N B n i else ∅ := by
  intro xz hxz
  obtain ⟨hblock, i, hT, hrel⟩ := mem_filter.mp hxz
  obtain ⟨hx, hz⟩ := mem_product.mp hblock
  obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
  let n := xz.1 - 1 + i.val
  have hi := i.isLt
  have hn : n ∈ Finset.Icc 1 (3 * N) := mem_Icc.mpr ⟨by dsimp [n]; omega, by dsimp [n]; omega⟩
  have hzall : ∀ k, xz.2 k ∈ Finset.Ico N (N + N) := by
    intro k
    simpa only [two_mul] using (Fintype.mem_piFinset.mp hz) k
  have hzhit := other_starts_mem_hits i hzall hrel
  have hxrec : n + 1 - i.val = xz.1 := by dsimp [n]; omega
  refine mem_biUnion.mpr ⟨i, mem_univ _, mem_biUnion.mpr ⟨n, hn, ?_⟩⟩
  rw [ite_eq_left hT]
  exact mem_image.mpr ⟨xz.2, hzhit, Prod.ext hxrec rfl⟩

theorem configurations_card_sum {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    (configurations (ι := ι) N B T).card ≤ B *
      ∑ n ∈ Finset.Icc 1 (3 * N), if T < (largeOddKernel B n : ℝ) then
        (PaperP1.SeveralKernelReceivers.hits (ι := ι) (roughSupport B n) B N N).card else 0 := by
  calc
    _ ≤ ((univ : Finset (Fin B)).biUnion fun i ↦
        (Finset.Icc 1 (3 * N)).biUnion fun n ↦
          if T < (largeOddKernel B n : ℝ) then anchorHosts (ι := ι) N B n i else ∅).card :=
      card_le_card (configurations_cover T hN hB)
    _ ≤ ∑ i : Fin B, ((Finset.Icc 1 (3 * N)).biUnion fun n ↦
        if T < (largeOddKernel B n : ℝ) then anchorHosts (ι := ι) N B n i else ∅).card := card_biUnion_le
    _ ≤ ∑ i : Fin B, ∑ n ∈ Finset.Icc 1 (3 * N),
        (if T < (largeOddKernel B n : ℝ) then anchorHosts (ι := ι) N B n i else ∅).card :=
      sum_le_sum (fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ _i : Fin B, ∑ n ∈ Finset.Icc 1 (3 * N), if T < (largeOddKernel B n : ℝ) then
        (PaperP1.SeveralKernelReceivers.hits (ι := ι) (roughSupport B n) B N N).card else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro n _
      split_ifs
      · exact card_image_le
      · exact le_rfl
    _ = _ := by simp

theorem configurations_weighted {N B : ℕ} (T : ℝ) (hN : 2 ≤ N) (hB : B ≤ N) :
    ((configurations (ι := ι) N B T).card : ℝ) ≤
      4 ^ Fintype.card ι * B * (N : ℝ) ^ Fintype.card ι *
        weightedTail (Fintype.card ι) B (3 * N) T := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 (3 * N)) :
      ((if T < (largeOddKernel B n : ℝ) then
        (PaperP1.SeveralKernelReceivers.hits (ι := ι) (roughSupport B n) B N N).card else 0 : ℕ) : ℝ) ≤
      4 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι *
        supportTail (Fintype.card ι) B T (roughSupport B n) := by
    by_cases hT : T < (largeOddKernel B n : ℝ)
    · rw [ite_eq_left hT, supportTail, PaperP1.WeightedKernelTail.supportTail,
        support_product, ite_eq_left hT]
      have h := PaperP1.SeveralKernelReceivers.hits_card (ι := ι)
        (P := roughSupport B n) (B := B) N N (by omega)
        (fun p hp ↦ prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1)
        ((PaperP1.LargeAnchorPairs.kernel_le_anchor (mem_Icc.mp hn).1).trans (mem_Icc.mp hn).2)
      rw [support_product, Nat.cast_mul, mul_pow] at h
      convert h using 1; ring
    · unfold supportTail PaperP1.WeightedKernelTail.supportTail
      rw [support_product, ite_eq_right hT, ite_eq_right hT, Nat.cast_zero, mul_zero, mul_zero]
  calc
    _ ≤ (B : ℝ) * ∑ n ∈ Finset.Icc 1 (3 * N),
        ((if T < (largeOddKernel B n : ℝ) then
          (PaperP1.SeveralKernelReceivers.hits (ι := ι) (roughSupport B n) B N N).card else 0 : ℕ) : ℝ) := by
      exact_mod_cast configurations_card_sum (ι := ι) T hN hB
    _ ≤ (B : ℝ) * ∑ n ∈ Finset.Icc 1 (3 * N),
        4 ^ Fintype.card ι * (N : ℝ) ^ Fintype.card ι *
          supportTail (Fintype.card ι) B T (roughSupport B n) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg B)
    _ = _ := by rw [← mul_sum]; unfold weightedTail; ring

theorem finite_exp_bound {N B : ℕ} (T τ : ℝ) (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N)
    (hT : 0 < T) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ((configurations (ι := ι) N B T).card : ℝ) ≤
      4 ^ Fintype.card ι * B * (N : ℝ) ^ Fintype.card ι * Real.sqrt (3 * N) * T ^ (-1 / 2 + τ) *
        Real.exp (2 * Real.sqrt B + Fintype.card ι * PaperP1.PowerSeriesTail.constant (1 + τ) * (B : ℝ) ^ (1 - τ)) := by
  have htail := weighted_tail_exp (Fintype.card ι) B (3 * N) T τ hB hT hτ hτhalf
  have hmul := mul_le_mul_of_nonneg_left htail
    (by positivity : (0 : ℝ) ≤ 4 ^ Fintype.card ι * B * (N : ℝ) ^ Fintype.card ι)
  refine (configurations_weighted (ι := ι) T hN hBN).trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hmul

end PaperP1.SeveralAnchorConfigurations
