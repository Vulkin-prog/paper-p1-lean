module

public import PaperP1.Model.OnceAllOriginalCoupling
public import PaperP1.Asymptotics.DependentPairSecondMomentUnderInputs
public import PaperP1.Asymptotics.CriticalPairNegligible

/-! # Rate-one original once/all coupling from the existing coarse geometry

The sharp O(a_N^2) second factorial moment is not assumed. The weaker
rate-one estimate already makes all three exact coupling errors negligible
relative to the first-order pair scale.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OnceAllCouplingUnderInputs

open PaperP1.Model PaperP1.OnceAllOriginalCoupling PaperP1.CoarseConnectedParameters

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters 4, Hypotheses p (ε / 16) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      second H N L ≤ (N : ℝ) ^ (-1 + ε) ∧
      correction H N L + totalVariation H N L + wasserstein H N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := DependentPairSecondMomentUnderInputs.uniform_good_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NS, _hNS, hs⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NF + NS, by omega, ?_⟩
  intro N hN L hband H
  have hsecond : second H N L ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    rw [second_eq_joint (by omega) H]
    exact hs N (by omega) L hband H
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hcost := good_bounds (L := L) (by omega : 2 ≤ N) H
  have hpos := Real.rpow_nonneg (Nat.cast_nonneg N) (-1 + ε / 2)
  constructor <;> nlinarith only [hsecond, hfactor, hcost.2.1, hcost.2.2.1, hcost.2.2.2, hpos]

theorem uniform_relative (C : ℝ) :
    ∃ p : Parameters 4, Hypotheses p (1 / 96) →
      CriticalPairNegligible.Negligible C (fun N L ↦
        correction (8 * (L + 1) : ℕ) N L + totalVariation (8 * (L + 1) : ℕ) N L +
          wasserstein (8 * (L + 1) : ℕ) N L) := by
  obtain ⟨p, hp⟩ := uniform_bound C (1 / 6) (by norm_num)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, _hN₀, h⟩ := hp (by norm_num at hgeo ⊢; exact hgeo)
  apply CriticalPairNegligible.of_power_bound C (5 / 6) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  have hb := good_bounds (L := L) (by omega : 2 ≤ N) (8 * (L + 1) : ℕ)
  have hn := add_nonneg (add_nonneg hb.1 (totalVariation_nonneg (8 * (L + 1) : ℕ) N L))
    (wasserstein_nonneg (8 * (L + 1) : ℕ) N L)
  rw [abs_of_nonneg hn]
  convert (h N hN L hband (8 * (L + 1) : ℕ)).2 using 1
  norm_num

end PaperP1.OnceAllCouplingUnderInputs
