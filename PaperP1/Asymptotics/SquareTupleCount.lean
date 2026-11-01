module

public import PaperP1.Asymptotics.ProfileTupleCount

/-! # Complete actual short split-product square-tuple count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareTupleCount

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles PaperP1.SplitOffsetProducts
open PaperP1.DyadicPatternWeights PaperP1.SplitKernelStates PaperP1.ProfileTupleCount

theorem square_tuple_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hv : 2 ≤ Fintype.card ι) (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ T : Finset (ι → ℕ),
      (∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧ IsSquare (∏ j, kernels A n j)) →
      (T.card : ℝ) ≤ (N : ℝ) ^ (mainExponent (Fintype.card ι) c + ε) := by
  classical
  obtain ⟨Np, hNp⟩ := profile_count (ι := ι) hv C hC c D A₀ (ε / 4) hc (by positivity)
  obtain ⟨Nc, hNc⟩ := profile_card_budget ι C c (ε / 2) hc (by positivity)
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitTupleExposure.source_height C D A₀
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop (max 1 (2 * Real.log (C + 1 : ℕ) / ε))))
  refine ⟨max 2 (max Np (max Nc (max Nh Nl))), ?_⟩
  intro N hN W A hW heven hcard hwidth hdegree hA T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 1 ≤ Real.log N := (le_max_left _ _).trans (hNl N (by omega))
  have hlogNpos : 0 < Real.log N := by linarith
  have hheightError : Real.log (C + 1 : ℕ) / (2 * Real.log N) ≤ ε / 4 := by
    have hlower := (le_max_right _ _).trans (hNl N (by omega))
    have hbudget := (div_le_iff₀ hε).mp hlower
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log N)).mpr
    nlinarith only [hbudget]
  let cells := fun J : Code ι C N A.card ↦ T.filter fun n ↦ Valid (kernels A n) J
  have hcells : ∀ J ∈ (univ : Finset (Code ι C N A.card)),
      ((cells J).card : ℝ) ≤ (N : ℝ) ^ (mainExponent (Fintype.card ι) c + ε / 2) := by
    intro J _
    have hp := hNp N (by omega) W A J hW heven hcard hwidth hdegree hA (cells J) (by
      intro n hnT
      obtain ⟨hnT', hvalid⟩ := mem_filter.mp hnT
      exact ⟨(hT n hnT').1, (hT n hnT').2, hvalid⟩)
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hcover : ∀ n ∈ T, ∃ J ∈ (univ : Finset (Code ι C N A.card)), n ∈ cells J := by
    intro n hnT
    have hq : ∀ j, 0 < kernels A n j := fun j ↦ kernel_pos A (n j)
    have hheight : ∀ j, kernels A n j ≤ height C N A.card := by
      intro j
      exact (hNh N (by omega) W (n j) A ((hT n hnT).1 j).1 ((hT n hnT).1 j).2 hwidth hA).2
    let J := actual_profile (kernels A n) hq C N A.card (by omega) hheight
    exact ⟨J, mem_univ _, mem_filter.mpr ⟨hnT, actual_profile_valid _ hq (by omega) hheight⟩⟩
  have hcount := PaperP1.FiniteCoverCount.cardinal_le T univ cells
    ((N : ℝ) ^ (mainExponent (Fintype.card ι) c + ε / 2)) hcover hcells
  have hcodes : ((univ : Finset (Code ι C N A.card)).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [card_univ] using hNc N (by omega) A.card hdegree
  calc
    _ ≤ ((univ : Finset (Code ι C N A.card)).card : ℝ) *
        (N : ℝ) ^ (mainExponent (Fintype.card ι) c + ε / 2) := hcount
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (mainExponent (Fintype.card ι) c + ε / 2) :=
      mul_le_mul_of_nonneg_right hcodes (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.SquareTupleCount
