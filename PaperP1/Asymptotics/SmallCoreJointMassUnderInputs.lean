module

public import PaperP1.Asymptotics.NoSingletonJointMassUnderInputs
public import PaperP1.Model.SmallCoreFamilyCover
public import PaperP1.Asymptotics.UniformIndependentDeficit
public import PaperP1.Asymptotics.SaturationDegrees

/-! # The remaining compatible ten-cores of sizes3..255 have joint mass N⁻¹ and source deficit mass N⁻³ᐟ² -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCoreJointMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CoarseConnectedParameters PaperP1.SubspaceFamilyRank

theorem uniform_mass (v C ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ∃ p : Parameters 255, Hypotheses p (ε / 8) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ 3 ≤ D.card),
        v ^ D.card * infiniteJointMoment L D) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := NoSingletonJointMassUnderInputs.uniform_weighted 255 v C ε hv.le hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NJ, _hNJ, hj⟩ := hp hgeo
  refine ⟨10 + NJ + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  apply hj N (by omega) L hband G hG
  intro D hD
  obtain ⟨hDC, hthree⟩ := mem_filter.mp hD
  obtain ⟨hDG, _htwo, hsmall, hcore, hq⟩ := (SmallCoreFamilyCover.mem_cores G D L).mp hDC
  have hc : infiniteCenteredCoefficient L D ≠ 0 := by
    intro hzero
    have h := RelationCoreMomentRatio.ten_core_ratio L D hL hq (by omega) hcore
    rw [hzero, mul_zero] at h
    exact (not_le_of_gt hq) h
  refine ⟨hDG, hthree, by omega, ?_⟩
  intro C hC
  exact ActualCanonicalComponents.nonzero_block_card L hL D C hc hC

theorem uniform_source (v C ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ∃ p : Parameters 255, Hypotheses p (ε / 16) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ 3 ≤ D.card),
        v ^ D.card * infiniteJointMoment L D * IndependentExtensionDeficit.deficit G D
          (span (fun x ↦ squareClassSpace x L) D) L v) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨p, hp⟩ := uniform_mass v C (ε / 2) hv (by positivity)
  obtain ⟨NE, _hNE, he⟩ := UniformIndependentDeficit.uniform_bound 255 v C (ε / 2) hv (by positivity)
  obtain ⟨NF, hf⟩ := SaturationDegrees.finite_conditions C 12 (by norm_num)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NJ, _hNJ, hj⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NJ + NE + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdef (D : Finset ℕ) (hD : D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ 3 ≤ D.card)) :
      IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L v ≤
        (N : ℝ) ^ (-1 / 2 + ε / 2) := by
    obtain ⟨hDG, _htwo, hsmall, _hcore, _hq⟩ :=
      (SmallCoreFamilyCover.mem_cores G D L).mp (mem_filter.mp hD).1
    have hDN := hDG.trans hG
    apply he N (by omega) L hband G hG D hDN (by omega)
    exact IntersectionExceptional.span_le_raw D L (by
      intro x hx
      have h := (mem_Ico.mp (hDN hx)).1
      omega)
  calc
    _ ≤ ∑ D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ 3 ≤ D.card),
        v ^ D.card * infiniteJointMoment L D * (N : ℝ) ^ (-1 / 2 + ε / 2) := by
      apply sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left (hdef D hD)
        (mul_nonneg (pow_nonneg hv.le _) (infiniteJointMoment_nonneg L D))
    _ = (∑ D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ 3 ≤ D.card),
        v ^ D.card * infiniteJointMoment L D) * (N : ℝ) ^ (-1 / 2 + ε / 2) := (sum_mul ..).symm
    _ ≤ (N : ℝ) ^ (-1 + ε / 2) * (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (hj N (by omega) L hband G hG) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.SmallCoreJointMassUnderInputs
