module

public import PaperP1.Model.ConnectedFourthReduction
public import PaperP1.Asymptotics.FourthRepeatedRunCost
public import PaperP1.Asymptotics.OverlappingPairProductCost
public import PaperP1.Asymptotics.NonDirectApartCost

/-! # The exact fourth cumulant differs from its connected sum by rate five thirds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthConnectedCumulant

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FourthRunFactorialCumulant PaperP1.ConnectedWindowFamilies

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |fourthFactorialCumulant (dyadicBlock N) L -
        24 * CompatibleActivitySplit.signed L (connectedFamilies (dyadicBlock N) L 4)| ≤
          (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := FourthRepeatedRunCost.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := OverlappingPairProductCost.uniform_repeated_square C (ε / 2) (by positivity)
  obtain ⟨NV, _hNV, hv⟩ := OverlappingPairProductCost.uniform_star_square C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := NonDirectApartCost.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 49 (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NR (max NS (max NV (max NA (max NL NF))))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  have hremainder := (hr N (by omega) L hband (dyadicBlock N) (subset_refl _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (show -2 + ε / 2 ≤ -5 / 3 + ε / 2 by linarith))
  have hrepeat := hs N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hstar := hv N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hapart := ha N (by omega) L hband
  have hfinite := ConnectedFourthReduction.finite_bound (dyadicBlock N) L hL
  calc
    _ ≤ 49 * (N : ℝ) ^ (-5 / 3 + ε / 2) := by linarith only [hfinite, hremainder, hrepeat, hstar, hapart]
    _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FourthConnectedCumulant
