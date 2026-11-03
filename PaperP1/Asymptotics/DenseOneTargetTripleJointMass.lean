module

public import PaperP1.Asymptotics.DenseEffectiveTargetCount
public import PaperP1.Asymptotics.PointwiseJointRankCap

/-! # Dense one-target crossings above a fixed pair have the true rank-limited joint cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseOneTargetTripleJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C η σ ε : ℝ) (hη : 0 < η) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = 2 → e ⊆ dyadicBlock N →
      ∀ S : Finset ℕ, S ⊆ dyadicBlock N →
      (∀ z ∈ S, z ∉ e ∧ η * L ≤ (OneTargetCrossing.rank e L z : ℝ) ∧
        (runRelativeNullity L (insert z e) : ℝ) ≤ σ * L) →
        (∑ z ∈ S, infiniteJointMoment L (insert z e)) ≤ (N : ℝ) ^ (-3 + σ + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := DenseEffectiveTargetCount.uniform_count 2 C η (ε / 2) hη (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := PointwiseJointRankCap.uniform_bound 3 C σ (ε / 2) hσ (by positivity)
  refine ⟨3 + NC + NP, by omega, ?_⟩
  intro N hN L hband e he heG S hSG hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hc N (by omega) L hband e he heG S hSG (fun z hz ↦ (hS z hz).2.1)
  have hpoint (z : ℕ) (hz : z ∈ S) :
      infiniteJointMoment L (insert z e) ≤ (N : ℝ) ^ (-3 + σ + ε / 2) := by
    apply hp N (by omega) L hband (insert z e)
      (insert_subset_iff.mpr ⟨hSG hz, heG⟩) _ (hS z hz).2.2
    rw [card_insert_of_notMem (hS z hz).1, he]
  calc
    _ ≤ ∑ _z ∈ S, (N : ℝ) ^ (-3 + σ + ε / 2) := sum_le_sum hpoint
    _ = (S.card : ℝ) * (N : ℝ) ^ (-3 + σ + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-3 + σ + ε / 2) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.DenseOneTargetTripleJointMass
