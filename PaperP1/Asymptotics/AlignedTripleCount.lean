module

public import PaperP1.Model.AlignedTripleFamilies
public import PaperP1.Asymptotics.JointFamilyProbabilityUnderBCN

/-! # An unconditional aligned-triple count and its BCN-dependent joint mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTripleCount

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AlignedTripleFamilies
  PaperP1.CriticalBandScale

theorem uniform_count (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ((families G L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NF, hfactor⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 25 20 ε hε
  refine ⟨max 2 (max NG NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : (G.card : ℝ) ≤ N := by exact_mod_cast (card_le_card hG).trans_eq (dyadicBlock_card N)
  obtain ⟨_, _, _, _, _, hB⟩ := hgeom N (by omega) L hband
  have hp := hfactor N (by omega) L hB
  have hp' : 25 * ((L : ℝ) + 1) ^ 20 ≤ (N : ℝ) ^ ε := by
    simpa only [abs_of_nonneg (by positivity : 0 ≤ 25 * ((L : ℝ) + 1) ^ 20)] using hp
  have hfinite : ((families G L).card : ℝ) ≤ (G.card : ℝ) * 25 * ((L : ℝ) + 1) ^ 20 := by
    exact_mod_cast card_bound G L
  calc
    _ ≤ (G.card : ℝ) * (25 * ((L : ℝ) + 1) ^ 20) := by simpa only [mul_assoc] using hfinite
    _ ≤ (N : ℝ) * (N : ℝ) ^ ε := mul_le_mul hcard hp' (by positivity) hn.le
    _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]

theorem uniform_joint_mass (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NC, hNC, hcount⟩ := uniform_count C η hη
  obtain ⟨NP, hprob⟩ := JointFamilyProbabilityUnderBCN.uniform_triple_probability c κ hc hBCN C η hη
  refine ⟨max NC NP, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ _I ∈ families G L, (N : ℝ) ^ (-3 / 2 + η) := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hIG, hcard, _⟩ := mem_families.mp hI
      exact hprob N (by omega) L hband I (hIG.trans hG) hcard
    _ = ((families G L).card : ℝ) * (N : ℝ) ^ (-3 / 2 + η) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 + η) * (N : ℝ) ^ (-3 / 2 + η) :=
      mul_le_mul_of_nonneg_right (hcount N (by omega) L hband G hG) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [η]; ring

end PaperP1.AlignedTripleCount
