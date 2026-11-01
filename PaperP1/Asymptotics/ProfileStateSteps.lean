module

public import PaperP1.Asymptotics.ProfileRecordCount

/-! # Actual cardinal transitions between successive exposure states -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProfileStateSteps

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles PaperP1.SplitOffsetProducts
open PaperP1.PrescribedPatternDivisors PaperP1.DyadicPatternWeights PaperP1.SplitKernelStates
open PaperP1.FiniteRefinementCount

theorem step_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hv : 2 ≤ Fintype.card ι) (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ, ∀ J : Code ι C N A.card,
      ∀ rank : ι → ℕ, ∀ k : ℕ, ∀ i : ι, Function.Injective rank → rank i = k →
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ T : Finset (ι → ℕ),
      (∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧
        IsSquare (∏ j, kernels A n j) ∧ Valid (kernels A n) J) →
      ((T.image (state A rank (k + 1))).card : ℝ) ≤ ((T.image (state A rank k)).card : ℝ) *
        (N : ℝ) ^ (PaperP1.ProfileExposureOrder.cost J A.card rank i + c * Fintype.card ι * Real.log 2 + ε) := by
  classical
  obtain ⟨N₀, hN₀⟩ := PaperP1.ProfileRecordCount.record_count (ι := ι) hv C hC c D A₀ ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W A J rank k i hrank hki hW heven hcard hwidth hdegree hA T hT
  apply refinement_bound T (state A rank k) (state A rank (k + 1)) (stepRecord A rank i)
  · intro n hn m hm hstate hrecord
    exact advance_determined A rank hrank k i hki n m (hT n hn).2.1 (hT m hm).2.1 hstate hrecord
  · intro p hp
    obtain ⟨n₀, hn₀, hp₀⟩ := mem_image.mp hp
    let e := prescribed (kernels A n₀) rank i
    apply hN₀ N hN W e A J rank i hrank hW heven hcard hwidth hdegree hA
    intro n hn
    obtain ⟨hnT, hnp⟩ := mem_filter.mp hn
    obtain ⟨hcomp, hsq, hvalid⟩ := hT n hnT
    exact ⟨hcomp, hsq, hvalid,
      prescribed_eq A rank k i hki n n₀ (hnp.trans hp₀.symm)⟩

theorem last_step_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      ∀ rank : ι → ℕ, ∀ k : ℕ, ∀ last : ι, Function.Injective rank → rank last = k →
      (∀ i, rank i ≤ rank last) →
      0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ T : Finset (ι → ℕ),
      (∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧ IsSquare (∏ j, kernels A n j)) →
      ((T.image (state A rank (k + 1))).card : ℝ) ≤ ((T.image (state A rank k)).card : ℝ) *
        (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  classical
  obtain ⟨N₀, hN₀⟩ := PaperP1.ComparableSplitProductCount.fixed_kernel_count C hC c D A₀ ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W A rank k last hrank hki hlast hW hcard hwidth hdegree hA T hT
  apply refinement_bound T (state A rank k) (state A rank (k + 1)) (fun n ↦ n last)
  · intro n hn m hm hstate hcentre
    exact advance_last_determined A rank hrank k last hki hlast n m (hT n hn).2 (hT m hm).2 hstate hcentre
  · intro p hp
    obtain ⟨n₀, hn₀, hp₀⟩ := mem_image.mp hp
    apply hN₀ N hN W (kernel A (n₀ last)) A hW hcard hwidth hdegree hA
    intro z hz
    obtain ⟨n, hn, hnz⟩ := mem_image.mp hz
    obtain ⟨hnT, hnp⟩ := mem_filter.mp hn
    have heq := last_kernel_eq A rank hrank k last hki hlast n n₀ (hT n hnT).2
      (hT n₀ hn₀).2 (hnp.trans hp₀.symm)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hnz] using ((hT n hnT).1 last).1
    · simpa only [hnz] using ((hT n hnT).1 last).2
    · simpa only [kernels, hnz] using heq

end PaperP1.ProfileStateSteps
