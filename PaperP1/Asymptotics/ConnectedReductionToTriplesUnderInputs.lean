module

public import PaperP1.Asymptotics.SharpCompatibleActivityUnderInputs
public import PaperP1.Asymptotics.SharpIncompatibleActivityUnderInputs

/-! # Complete main Proposition 15.10 under the existing finite geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedReductionToTriplesUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

structure Parameters (R : ℕ) where
  compatible : SharpConnectedSeedParameters.Parameters R
  incompatible : SharpIncompatibleActivityUnderInputs.Parameters R

structure Hypotheses {R : ℕ} (p : Parameters R) (ε : ℝ) : Prop where
  compatible : SharpConnectedSeedParameters.Hypotheses p.compatible (ε / 8)
  incompatible : SharpIncompatibleActivityUnderInputs.Hypotheses p.incompatible (ε / 2)

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      F ⊆ connectedFamilies G L r →
      (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
        (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) +
        (N : ℝ) ^ (-4 / 3 + ε) ∧
      CompatibleActivitySplit.incompatibleAbsolute L F ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨pc, hc⟩ := SharpCompatibleActivityUnderInputs.uniform_range R C (ε / 2) (by positivity)
  obtain ⟨pi, hi⟩ := SharpIncompatibleActivityUnderInputs.uniform_range R C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨⟨pc, pi⟩, ?_⟩
  intro hgeo
  have hs : (ε / 2) / 4 = ε / 8 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hs] using hgeo.compatible)
  obtain ⟨NI, _hNI, hi⟩ := hi hgeo.incompatible
  refine ⟨10 + NC + NI + NF, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ infiniteJointMoment L I = 0
  let FZ := F.filter P
  let FP := F.filter fun I ↦ ¬ P I
  have hZ : (∑ I ∈ FZ, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) :=
    hi N (by omega) L hband r hthree hcap G hG FZ
      (fun I hI ↦ hF (mem_filter.mp hI).1) (fun I hI ↦ (mem_filter.mp hI).2)
  have hP : (∑ I ∈ FP, |infiniteCenteredCoefficient L I|) ≤
      (N : ℝ) ^ (ε / 2) * CompatibleActivitySplit.absolute L (connectedFamilies G L 3) +
      (N : ℝ) ^ (-4 / 3 + ε / 2) :=
    hc N (by omega) L hband r hthree hcap G hG FP (fun I hI ↦ hF (mem_filter.mp hI).1)
      (fun I hI ↦ lt_of_le_of_ne (infiniteJointMoment_nonneg L I) (Ne.symm (mem_filter.mp hI).2))
  have hA : CompatibleActivitySplit.absolute L (connectedFamilies G L 3) ≤
      CompatibleActivitySplit.absolute L (G.powersetCard 3) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun I _ _ ↦ abs_nonneg _)
  have hA0 : 0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 3) := sum_nonneg fun I _ ↦ abs_nonneg _
  have hcoeff : (N : ℝ) ^ (ε / 2) * CompatibleActivitySplit.absolute L (connectedFamilies G L 3) ≤
      (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) :=
    (mul_le_mul_of_nonneg_left hA (by positivity)).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hA0)
  have hZweak : (∑ I ∈ FZ, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) :=
    hZ.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hfactor : 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ |infiniteCenteredCoefficient L I|)
  change (∑ I ∈ FZ, |infiniteCenteredCoefficient L I|) +
    (∑ I ∈ FP, |infiniteCenteredCoefficient L I|) = _ at hsplit
  constructor
  · linarith only [hZweak, hP, hcoeff, hfactor, hsplit]
  · exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))

theorem article_15_10 (r : ℕ) (hr : 4 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters r, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (connectedFamilies G L r) ≤
        (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) +
        (N : ℝ) ^ (-4 / 3 + ε) ∧
      CompatibleActivitySplit.incompatibleAbsolute L (connectedFamilies G L r) ≤
        (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨p, hp⟩ := uniform_range r C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact h N hN L hband r (by omega) le_rfl G hG (connectedFamilies G L r) Subset.rfl

end PaperP1.ConnectedReductionToTriplesUnderInputs
