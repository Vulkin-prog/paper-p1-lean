module

public import PaperP1.Model.ConnectedFourthReduction
public import PaperP1.Asymptotics.FourthRepeatedRunCostUnderInputs
public import PaperP1.Asymptotics.OverlappingPairProductCostUnderInputs
public import PaperP1.Asymptotics.NonDirectApartCostUnderInputs

/-! # The exact fourth cumulant differs from its connected sum by rate five thirds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthConnectedCumulantUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FourthRunFactorialCumulant PaperP1.ConnectedWindowFamilies

structure Parameters where
  triple : FixedMomentInputs.Parameters 3
  repeatedPair : FinitePairDeficitInputs.Parameters
  repeatedSquare : FinitePairDeficitInputs.Parameters
  starSquare : FinitePairDeficitInputs.Parameters
  apartPair : FinitePairDeficitInputs.Parameters
  apartPartition : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  triple : FixedMomentInputs.Hypotheses p.triple ε
  repeatedPair : FinitePairDeficitInputs.Hypotheses p.repeatedPair (GeneralGraphHostCount.sizeCap (1 / 100))
  repeatedSquare : FinitePairDeficitInputs.Hypotheses p.repeatedSquare (GeneralGraphHostCount.sizeCap (1 / 100))
  starSquare : FinitePairDeficitInputs.Hypotheses p.starSquare (GeneralGraphHostCount.sizeCap (1 / 100))
  apartPair : FinitePairDeficitInputs.Hypotheses p.apartPair (GeneralGraphHostCount.sizeCap (1 / 100))
  apartPartition : FinitePairDeficitInputs.Hypotheses p.apartPartition (GeneralGraphHostCount.sizeCap (ε / 2048))

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |fourthFactorialCumulant (dyadicBlock N) L -
        24 * CompatibleActivitySplit.signed L (connectedFamilies (dyadicBlock N) L 4)| ≤
          (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨pt, pr, hr⟩ := FourthRepeatedRunCostUnderInputs.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨ps, hs⟩ := OverlappingPairProductCostUnderInputs.uniform_repeated_square C (ε / 2) (by positivity)
  obtain ⟨pv, hv⟩ := OverlappingPairProductCostUnderInputs.uniform_star_square C (ε / 2) (by positivity)
  obtain ⟨pa, pw, ha⟩ := NonDirectApartCostUnderInputs.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 49 (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨pt, pr, ps, pv, pa, pw⟩, ?_⟩
  intro hgeo
  obtain ⟨NR, _hNR, hr⟩ := hr (by simpa only [show 2 * (ε / 2) = ε by ring] using hgeo.triple) hgeo.repeatedPair
  obtain ⟨NS, _hNS, hs⟩ := hs hgeo.repeatedSquare
  obtain ⟨NV, _hNV, hv⟩ := hv hgeo.starSquare
  obtain ⟨NA, _hNA, ha⟩ := ha hgeo.apartPair
    (by simpa only [show ε / 2 / 1024 = ε / 2048 by ring] using hgeo.apartPartition)
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

end PaperP1.FourthConnectedCumulantUnderInputs
