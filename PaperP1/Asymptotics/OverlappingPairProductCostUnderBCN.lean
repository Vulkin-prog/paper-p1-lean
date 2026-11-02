module

public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.PairActivityUnderBCN

/-! # Actual repeated-edge and shared-vertex covariance product costs at scale N^(-3/2)

The per-site row estimate and local marginal cap are unconditional. Only
the global pair-activity bound uses the existing explicit BCN argument.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OverlappingPairProductCostUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairRowActivity

theorem uniform_repeated_square (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      repeatedSquare G L ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hcap⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NA, _hNA, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption K (-3 / 2 + η) η hη
  refine ⟨max 2 (max NP (max NA NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) :=
      repeated_square_bound G L (K / N) (fun x hx ↦ hcap N (by omega) L hband x (hG hx))
    _ ≤ (K / N) * (N : ℝ) ^ (-1 / 2 + η) :=
      mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity)
    _ = K * (N : ℝ) ^ (-3 / 2 + η) := by
      rw [show -3 / 2 + η = (-1 / 2 + η) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_star_square (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      starSquare G L ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NP, _hNP, hcap⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NR, _hNR, hrow⟩ := ActualPairRowActivity.uniform_absolute_row C η hη
  obtain ⟨NA, _hNA, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (2 * K) (-3 / 2 + 2 * η) η hη
  refine ⟨max 2 (max NP (max NR (max NA NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpower : 0 ≤ (N : ℝ) ^ η := Real.rpow_nonneg hn.le _
  calc
    _ ≤ 2 * (N : ℝ) ^ η * (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) :=
      star_square_bound G L (K / N) ((N : ℝ) ^ η) hpower
        (fun x hx ↦ hcap N (by omega) L hband x (hG hx))
        (fun x hx ↦ hrow N (by omega) L hband G hG x (hG hx))
    _ ≤ 2 * (N : ℝ) ^ η * (K / N) * (N : ℝ) ^ (-1 / 2 + η) :=
      mul_le_mul_of_nonneg_left (hpair N (by omega) L hband G hG) (by positivity)
    _ = 2 * K * (N : ℝ) ^ (-3 / 2 + 2 * η) := by
      rw [show -3 / 2 + 2 * η = (η + (-1 / 2 + η)) - 1 by ring,
        Real.rpow_sub hn, Real.rpow_one, Real.rpow_add hn η (-1 / 2 + η)]
      ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + 2 * η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.OverlappingPairProductCostUnderBCN
