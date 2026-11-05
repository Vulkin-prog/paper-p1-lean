module

public import PaperP1.Asymptotics.RetainedPairLeakageLimit
public import PaperP1.Asymptotics.RetainedIndependentDeficitRates
public import PaperP1.Model.RetainedReferenceCardinalityTheorem
public import PaperP1.Model.RetainedPairCountSource

/-! # Companion T22.6: the complete actual modified-moment identity, positive deficits and weighted pair leakage -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModifiedMomentDecomposition

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RegularStarts
  PaperP1.RetainedActiveSubsetMoments PaperP1.RetainedModifiedMomentDecomposition
  PaperP1.RetainedCardinalityDeficits PaperP1.RetainedExceptionalEvent

theorem uniform_deficit (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      (∑' r : ℕ, (2 : ℝ) ^ r * secondCoefficient H N L r) ≤ (N : ℝ) ^ (-7 / 6 + ε) := by
  obtain ⟨ND, _hND, hd⟩ := RetainedIndependentDeficitRates.second_bound C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + ND + NG, by omega, ?_⟩
  intro N hN L hband H
  have hN2 : 2 ≤ N := by omega
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  rw [← RetainedReferenceCardinalityTheorem.Gtotal_eq_tsum hN2 H]
  change (∑ r ∈ range ((regularStarts N L).card + 1), (2 : ℝ) ^ r * secondCoefficient H N L r) ≤ _
  rw [← RetainedDeficitGrouping.secondMass_grouped hN2 hL H]
  exact hd N (by omega) L hband H

theorem companion_T22_6 (C : ℝ) :
    (∀ N L : ℕ, 2 ≤ N → 0 < L → ∀ H : ℝ, ∀ r : ℕ, 1 ≤ r →
        modifiedChooseMoment H N L r = ((regularStarts N L).card.choose r : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ r -
          firstCoefficient N L r - directLeakage H N L r + pairBinomialTerm H N L r - secondCoefficient H N L r - pairLeakage H N L r ∧
        0 ≤ firstCoefficient N L r ∧ 0 ≤ directLeakage H N L r ∧ 0 ≤ secondCoefficient H N L r ∧ 0 ≤ pairLeakage H N L r) ∧
      (∀ H : ℝ, ∀ N L r : ℕ, r < 2 → pairBinomialTerm H N L r = 0 ∧ secondCoefficient H N L r = 0 ∧ pairLeakage H N L r = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑' r : ℕ, (2 : ℝ) ^ r * secondCoefficient (8 * (L + 1) : ℕ) N L r) ≤ (N : ℝ) ^ (-1 + ε) ∧
        (∑' r : ℕ, (2 : ℝ) ^ r * pairLeakage (8 * (L + 1) : ℕ) N L r) ≤ ε * SecondFactorialCorrection.value N L) := by
  have hp := RetainedPairLeakageLimit.uniform_relative C
  refine ⟨?_, ?_, ?_⟩
  · intro N L hN hL H r hr
    exact ⟨source_identity hN hL H r hr, firstCoefficient_nonneg N L r, directLeakage_nonneg H N L r,
      secondCoefficient_nonneg H N L r, pairLeakage_nonneg H N L r⟩
  · intro H N L r hr
    exact ⟨by rw [pairBinomialTerm, ite_eq_left hr], secondCoefficient_zero_small H N L r hr, pairLeakage_zero_small H N L r hr⟩
  · intro ε hε
    obtain ⟨NL, _hNL, hl⟩ := hp ε hε
    obtain ⟨ND, _hND, hd⟩ := uniform_deficit C ε hε
    refine ⟨10 + NL + ND, by omega, ?_⟩
    intro N hN L hband
    have hweak : (N : ℝ) ^ (-7 / 6 + ε) ≤ (N : ℝ) ^ (-1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
    exact ⟨(hd N (by omega) L hband _).trans hweak, hl N (by omega) L hband⟩

end PaperP1.ModifiedMomentDecomposition
