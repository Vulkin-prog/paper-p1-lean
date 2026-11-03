module

public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.FinitePairActivityInputs

/-! # Repeated-edge and shared-vertex covariance products have the stronger rate five thirds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OverlappingPairProductCostUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairRowActivity

theorem uniform_repeated_square (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      repeatedSquare G L ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hcap⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨p, hp⟩ := FinitePairActivityInputs.uniform_pair C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption K (-5 / 3 + η) η hη
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NA, _hNA, hpair⟩ := hp hgeo
  refine ⟨max 2 (max NP (max NA NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) :=
      repeated_square_bound G L (K / N) (fun x hx ↦ hcap N (by omega) L hband x (hG hx))
    _ ≤ (K / N) * (N : ℝ) ^ (-2 / 3 + η) :=
      mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity)
    _ = K * (N : ℝ) ^ (-5 / 3 + η) := by
      rw [show -5 / 3 + η = (-2 / 3 + η) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-5 / 3 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_star_square (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      starSquare G L ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hcap⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NR, _hNR, hrow⟩ := ActualPairRowActivity.uniform_absolute_row C η hη
  obtain ⟨p, hp⟩ := FinitePairActivityInputs.uniform_pair C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (2 * K) (-5 / 3 + 2 * η) η hη
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NA, _hNA, hpair⟩ := hp hgeo
  refine ⟨max 2 (max NP (max NR (max NA NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpower : 0 ≤ (N : ℝ) ^ η := Real.rpow_nonneg hn.le _
  calc
    _ ≤ 2 * (N : ℝ) ^ η * (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) :=
      star_square_bound G L (K / N) ((N : ℝ) ^ η) hpower
        (fun x hx ↦ hcap N (by omega) L hband x (hG hx))
        (fun x hx ↦ hrow N (by omega) L hband G hG x (hG hx))
    _ ≤ 2 * (N : ℝ) ^ η * (K / N) * (N : ℝ) ^ (-2 / 3 + η) :=
      mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity)
    _ = 2 * K * (N : ℝ) ^ (-5 / 3 + 2 * η) := by
      rw [show -5 / 3 + 2 * η = (η + (-2 / 3 + η)) - 1 by ring,
        Real.rpow_sub hn, Real.rpow_one, Real.rpow_add hn η (-2 / 3 + η)]
      ring
    _ ≤ (N : ℝ) ^ ((-5 / 3 + 2 * η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.OverlappingPairProductCostUnderInputs
