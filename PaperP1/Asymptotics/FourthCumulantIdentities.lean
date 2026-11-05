module

public import PaperP1.Asymptotics.FourthConnectedCumulant
public import PaperP1.Asymptotics.SharpIncompatibleActivity
public import PaperP1.Model.RegularCumulantTransfer

/-! # The complete three literal identities of main Lemma 16.1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthCumulantIdentities

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FourthRunFactorialCumulant PaperP1.ConnectedWindowFamilies

theorem article_16_1 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let F := connectedFamilies (dyadicBlock N) L 4
      let κ₄ := fourthFactorialCumulant (dyadicBlock N) L
      let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
      0 ≤ CompatibleActivitySplit.positive L F ∧
      |κ₄ - 24 * CompatibleActivitySplit.signed L F| ≤ (N : ℝ) ^ (-5 / 3 + ε) ∧
      |CompatibleActivitySplit.signed L F - CompatibleActivitySplit.positive L F| ≤
        (N : ℝ) ^ (-3 / 2 + ε) ∧
      |κ₄ + 3 * α ^ 2 - (3 * α ^ 2 + 24 * CompatibleActivitySplit.positive L F)| ≤
        (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := FourthConnectedCumulant.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NI, _hNI, hi⟩ := SharpIncompatibleActivity.uniform_range 4 C (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 25 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NI (max NL NF))), by omega, ?_⟩
  intro N hN L hband
  dsimp only
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  let F := connectedFamilies (dyadicBlock N) L 4
  have hinc : CompatibleActivitySplit.incompatibleAbsolute L F ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) :=
    hi N (by omega) L hband 4 (by norm_num) le_rfl (dyadicBlock N) (subset_refl _)
      (F.filter (fun I ↦ infiniteJointMoment L I = 0)) (filter_subset _ _)
      (fun _ hI ↦ (mem_filter.mp hI).2)
  have hs := (CompatibleActivitySplit.signed_error L F).trans hinc
  have hconn := hc N (by omega) L hband
  have hcweak := hconn.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (show -5 / 3 + ε / 2 ≤ -3 / 2 + ε / 2 by linarith))
  refine ⟨CompatibleActivitySplit.positive_nonneg L hL F,
    hconn.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])),
    hs.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])), ?_⟩
  have htriangle := abs_add_le
    (fourthFactorialCumulant (dyadicBlock N) L - 24 * CompatibleActivitySplit.signed L F)
    (24 * (CompatibleActivitySplit.signed L F - CompatibleActivitySplit.positive L F))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)] at htriangle
  have halgebra : fourthFactorialCumulant (dyadicBlock N) L - 24 * CompatibleActivitySplit.signed L F +
      24 * (CompatibleActivitySplit.signed L F - CompatibleActivitySplit.positive L F) =
      fourthFactorialCumulant (dyadicBlock N) L +
        3 * RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ^ 2 -
        (3 * RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ^ 2 +
          24 * CompatibleActivitySplit.positive L F) := by ring
  rw [halgebra] at htriangle
  calc
    _ ≤ 25 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by linarith only [htriangle, hcweak, hs]
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FourthCumulantIdentities
