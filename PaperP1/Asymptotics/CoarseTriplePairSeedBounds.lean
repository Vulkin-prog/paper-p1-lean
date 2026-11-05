module

public import PaperP1.Model.CoarseTriplePairSeeds
public import PaperP1.Asymptotics.WeakPairActivity
public import PaperP1.Asymptotics.NonalignedPairActivity
public import PaperP1.Asymptotics.BoundaryAlignedActivity
public import PaperP1.Asymptotics.DependentPairSeedPropagation

/-! # Actual weak, nonaligned and boundary pair seeds and all fixed containing families have coarse rate1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseTriplePairSeedBounds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_activity (θ C ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        CompatibleActivitySplit.absolute L (CoarseTriplePairSeeds.pairs N L θ) ≤
          (N : ℝ) ^ (-1 + θ + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := NonalignedPairActivity.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := WeakPairActivityAsymptotic.uniform_activity C θ (ε / 2) hθ (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := BoundaryAlignedActivity.height_one C (ε / 2) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := BoundaryAlignedActivity.height_two C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 + θ + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NA + NW + NB + ND + NF, by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + θ + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hθ])
  have hweak := hw N (by omega) L hband (dyadicBlock N) Subset.rfl
  have hnon := (ha N (by omega) L hband).trans hpow
  have hone := (hb N (by omega) L hband).trans hpow
  have htwo := (hd N (by omega) L hband).2.trans hpow
  have hfinite := CoarseTriplePairSeeds.activity_bound N L θ
  have hfactor : 4 * (N : ℝ) ^ (-1 + θ + ε / 2) ≤ (N : ℝ) ^ (-1 + θ + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hweak, hnon, hone, htwo, hfinite, hfactor]

theorem uniform_extensions (k : ℕ) (θ C ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
        (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = 2 + k ∧
          ∃ e ∈ CoarseTriplePairSeeds.pairs N L θ, e ⊆ T) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + θ + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := uniform_activity θ C (ε / 4) hθ (by positivity)
  obtain ⟨NR, hr⟩ := DependentPairSeedPropagation.uniform_bound k C (ε / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * ((2 + k).factorial : ℝ))
    (-1 + θ + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NP + NR + NG + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hseed := hp N (by omega) L hband
  have hprop := hr N (by omega) L hL hband (CoarseTriplePairSeeds.pairs N L θ)
    (fun _ he ↦ ((CoarseTriplePairSeeds.mem_pairs N L θ _).mp he).1) F hF
  calc
    _ ≤ (2 * ((2 + k).factorial : ℝ)) * (N : ℝ) ^ (ε / 4) *
        (N : ℝ) ^ (-1 + θ + ε / 4) := hprop.trans
      (mul_le_mul_of_nonneg_left hseed (mul_nonneg (by positivity) (Real.rpow_nonneg hn.le _)))
    _ = (2 * ((2 + k).factorial : ℝ)) * (N : ℝ) ^ (-1 + θ + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

end PaperP1.CoarseTriplePairSeedBounds
