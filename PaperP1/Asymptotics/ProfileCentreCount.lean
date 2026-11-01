module

public import PaperP1.Arithmetic.ProfileExposureOrder

/-! # Applying T5.2 with a fixed size profile and actual prescribed divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProfileCentreCount

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles PaperP1.SplitOffsetProducts
open PaperP1.ExposureWeights PaperP1.PrescribedPatternDivisors PaperP1.DyadicPatternWeights

theorem centre_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ,
      ∀ J : Code ι C N A.card, ∀ rank : ι → ℕ, ∀ i : ι,
      Function.Injective rank → 0 < W → Even A.card → 2 ≤ A.card →
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ → (A.card : ℝ) ≤ c * Real.log (Real.log N) →
      (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
      (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ ∃ q : ι → ℕ,
        q i = kernel A n ∧ (∀ j, Squarefree (q j)) ∧ IsSquare (∏ j, q j) ∧
          Valid q J ∧ prescribed q rank i = e) →
      (S.card : ℝ) ≤ (N : ℝ) ^
        (PaperP1.ProfileExposureOrder.cost J A.card rank i + c * Real.log 2 + ε) := by
  let F := (2 : ℝ) ^ (patterns : Finset (Finset ι)).card
  obtain ⟨Np, hNp⟩ := PaperP1.ComparableSplitProductCount.constant_upper_count C hC c D A₀ F ε hc hε
  refine ⟨max 2 Np, ?_⟩
  intro N hN W e A J rank i hrank hW heven hcard hwidth hdegree hA S hS
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  by_cases hnon : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hnon
    obtain ⟨_, _, q₀, _, hq₀, hsq₀, hvalid₀, he₀⟩ := hS n₀ hn₀
    have hδ : PaperP1.ProfileExposureOrder.delta J rank i ≤ Real.log e / Real.log N := by
      rw [← he₀]
      exact PaperP1.ProfileExposureOrder.delta_lower q₀ J (by omega) hvalid₀ rank hrank i
    have hcount := hNp N (by omega) W e A (degree patterns (weight J) i)
      hW heven hcard hwidth hdegree hA S (by
        intro n hnS
        obtain ⟨hnlo, hnhi, q, hqi, hq, hsq, hvalid, he⟩ := hS n hnS
        have hdiv := prescribed_dvd_coordinate q hq hsq rank i
        have hupper := coordinate_upper q hq hsq J (by omega) hvalid i
        rw [he, hqi] at hdiv
        rw [hqi] at hupper
        exact ⟨hnlo, hnhi, hdiv, hupper⟩)
    apply hcount.trans
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hd : (0 : ℝ) ≤ A.card := by positivity
    have hδdiv := div_le_div_of_nonneg_right hδ hd
    unfold PaperP1.SelectedQuadraticCells.baseExponent PaperP1.ProfileExposureOrder.cost
    linarith
  · have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hnon
    rw [hempty, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (by positivity) _

end PaperP1.ProfileCentreCount
