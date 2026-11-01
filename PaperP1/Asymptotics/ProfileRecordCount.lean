module

public import PaperP1.Asymptotics.ProfileCentreCount
public import PaperP1.Arithmetic.SplitFreshFamilies
public import PaperP1.Combinatorics.FiniteRefinementCount

/-! # Counting actual one-step records with the prescribed divisor fixed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProfileRecordCount

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles PaperP1.SplitOffsetProducts
open PaperP1.PrescribedPatternDivisors PaperP1.DyadicPatternWeights PaperP1.SplitKernelStates
open PaperP1.FiniteRefinementCount

theorem record_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hv : 2 ≤ Fintype.card ι) (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ J : Code ι C N A.card,
      ∀ rank : ι → ℕ, ∀ i : ι, Function.Injective rank →
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ T : Finset (ι → ℕ),
      (∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧
        IsSquare (∏ j, kernels A n j) ∧ Valid (kernels A n) J ∧ prescribed (kernels A n) rank i = e) →
      ((T.image (stepRecord A rank i)).card : ℝ) ≤
        (N : ℝ) ^ (PaperP1.ProfileExposureOrder.cost J A.card rank i + c * Fintype.card ι * Real.log 2 + ε) := by
  let B := 2 ^ (Fintype.card ι - 1)
  have hB : 2 ≤ B := by
    exact (by norm_num : 2 = 2 ^ 1).le.trans
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega))
  obtain ⟨Nc, hNc⟩ := PaperP1.ProfileCentreCount.centre_count (ι := ι) C hC c D A₀ (ε / 2) hc (by positivity)
  obtain ⟨Na, hNa⟩ := PaperP1.GrowingDegreePrimeBudget.exponential_prime_budget_additive
    c (C + 1 : ℕ) (ε / 2) hc (by exact_mod_cast (show 1 ≤ C + 1 by omega))
    (by positivity) B (by exact_mod_cast (show 1 < B by omega))
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitTupleExposure.source_height C D A₀
  refine ⟨max 2 (max Nc (max Na Nh)), ?_⟩
  intro N hN W e A J rank i hrank hW heven hcard hwidth hdegree hA T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let α := PaperP1.ProfileExposureOrder.cost J A.card rank i + c * Real.log 2 + ε / 2
  let β := c * ((Fintype.card ι : ℝ) - 1) * Real.log 2 + ε / 2
  have hcentres : ((T.image fun n ↦ n i).card : ℝ) ≤ (N : ℝ) ^ α := by
    apply hNc N (by omega) W e A J rank i hrank hW heven hcard hwidth hdegree hA
    intro z hz
    obtain ⟨n, hnT, hnz⟩ := mem_image.mp hz
    obtain ⟨hcomp, hsq, hvalid, he⟩ := hT n hnT
    refine ⟨?_, ?_, kernels A n, ?_, kernels_squarefree A n, hsq, hvalid, he⟩
    · simpa only [hnz] using (hcomp i).1
    · simpa only [hnz] using (hcomp i).2
    · simp only [kernels, hnz]
  have hfresh : ∀ z ∈ T.image (fun n ↦ n i),
      (((T.filter fun n ↦ n i = z).image fun n ↦ (stepRecord A rank i n).2).card : ℝ) ≤ (N : ℝ) ^ β := by
    intro z hz
    obtain ⟨n₀, hn₀, hn₀z⟩ := mem_image.mp hz
    have hcomp := (hT n₀ hn₀).1 i
    have hheight := (hNh N (by omega) W z A (by simpa only [hn₀z] using hcomp.1)
      (by simpa only [hn₀z] using hcomp.2) hwidth hA).2
    have hheightR : (kernel A z : ℝ) ≤ (((C + 1 : ℕ) : ℝ) * N) ^ A.card := by exact_mod_cast hheight
    have hfinite := PaperP1.SplitFreshFamilies.family_card_le A rank i (T.filter fun n ↦ n i = z) z e (by
      intro n hnT
      obtain ⟨hnT', hnz⟩ := mem_filter.mp hnT
      exact ⟨hnz, (hT n hnT').2.2.2, (hT n hnT').2.1⟩)
    have hfiniteR : (((T.filter fun n ↦ n i = z).image fun n ↦ (stepRecord A rank i n).2).card : ℝ) ≤
        (B : ℝ) ^ (kernel A z).primeFactors.card := by
      exact_mod_cast hfinite
    have hp := hNa N (by omega) (kernel A z) A.card (kernel_pos A z) hdegree hheightR
    have hlB : Real.log (B : ℝ) = ((Fintype.card ι : ℝ) - 1) * Real.log 2 := by
      dsimp [B]
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
      norm_num
    rw [hlB] at hp
    exact hfiniteR.trans (by simpa only [β, mul_assoc] using hp)
  have hrecord := pair_image_bound T (fun n ↦ n i) (fun n ↦ (stepRecord A rank i n).2)
    ((N : ℝ) ^ α) ((N : ℝ) ^ β) (Real.rpow_nonneg hn.le _) hcentres hfresh
  change ((T.image (stepRecord A rank i)).card : ℝ) ≤ (N : ℝ) ^ α * (N : ℝ) ^ β at hrecord
  have heq : α + β = PaperP1.ProfileExposureOrder.cost J A.card rank i + c * Fintype.card ι * Real.log 2 + ε := by
    dsimp [α, β]
    ring
  rw [← Real.rpow_add hn, heq] at hrecord
  exact hrecord

end PaperP1.ProfileRecordCount
