module

public import PaperP1.Asymptotics.HardNonalignedTripleCount
public import PaperP1.Asymptotics.JointFamilyProbability

/-! # Actual mass of the three-strong-nonaligned-pair population

The internal subpower host count and actual pointwise probability estimate
are combined before any original subground is selected.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardNonalignedTripleMass

open Finset Model Model.InfiniteStarts SharpTripleResidual ConnectedWindowFamilies

theorem uniform_mass (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      mass G L θ ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc⟩ := HardNonalignedTripleCount.uniform_count C θ (ε / 2) hθ (by positivity)
  obtain ⟨NP, hp⟩ := JointFamilyProbability.uniform_triple_probability C (ε / 2) (by positivity)
  refine ⟨4 + NC + NP, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ hosts G L θ) :
      infiniteJointMoment L T ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    obtain ⟨hconnected, _hHard⟩ := mem_filter.mp hT
    obtain ⟨hTp, _hconn⟩ := mem_filter.mp hconnected
    obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp hTp
    exact hp N (by omega) L hband T (hTG.trans hG) hcard
  calc
    _ ≤ ∑ T ∈ hosts G L θ, (N : ℝ) ^ (-3 / 2 + ε / 2) := sum_le_sum hpoint
    _ = ((hosts G L θ).card : ℝ) * (N : ℝ) ^ (-3 / 2 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hc N (by omega) L hband G hG) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.HardNonalignedTripleMass
