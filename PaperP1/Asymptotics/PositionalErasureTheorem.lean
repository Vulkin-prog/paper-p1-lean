module

public import PaperP1.Asymptotics.PositionalOriginalDeletion
public import PaperP1.Asymptotics.PositionalBackgroundMoments
public import PaperP1.Asymptotics.OriginalDeletedIntensity
public import PaperP1.Asymptotics.PositionalOriginalCovariance
public import PaperP1.Asymptotics.PositionalDeletedCountCumulant
public import PaperP1.Asymptotics.SharpOnceAllCoupling

/-! # Complete unconditional companion T19.10 on the original fields and natural coupling

The exact single-arrival intensities, factorial covariance matrices and actual
count projections are retained. The sharp two-edge constant precedes epsilon.
The summed L1 field estimate implies the printed summed total-variation estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalErasureTheorem

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw
  PaperP1.PositionalDeletedFields PaperP1.PositionalFactorialCovariance
  PaperP1.PositionalCountProjection PaperP1.OnceAllOriginalCoupling

theorem companion_T19_10 (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let H : ℝ := (8 * (L + 1) : ℕ)
      let G := dyadicBlock N
      let E := GoodEdgeCompression.goodEdges H N L
      let t := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
      let U := PositionalMarkedPairExpansion.background G E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      PositivePositionalConvolution.IsProbability U ∧
      ‖onceLaw E G L - U‖ + ‖isolatedLaw E G L - U‖ ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      (∑ x ∈ G, |mean (onceLaw E G L) x - t x|) +
        (∑ x ∈ G, |mean (isolatedLaw E G L) x - t x|) ≤ (N : ℝ) ^ (-1 + ε) ∧
      (∑ z ∈ G ×ˢ G, |covariance (onceLaw E G L) z.1 z.2|) +
        (∑ z ∈ G ×ˢ G, |covariance (isolatedLaw E G L) z.1 z.2|) ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      |PositionalCountCumulant.scalar (projection (onceLaw E G L))| +
        |PositionalCountCumulant.scalar (projection (isolatedLaw E G L))| ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      second H N L ≤ K * SecondFactorialCorrection.value N L ^ 2 ∧
      0 ≤ correction H N L ∧ correction H N L ≤ second H N L / 2 ∧
      totalVariation H N L ≤ second H N L / 2 ∧ wasserstein H N L ≤ second H N L := by
  obtain ⟨K, hK, NS, _hNS, hs⟩ := SharpOnceAllCoupling.companion_T19_10_sharp C
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨NF, _hNF, hf⟩ := PositionalOriginalDeletion.uniform_norm_bound C (ε / 2) (by positivity)
  obtain ⟨NI, _hNI, hi⟩ := OriginalDeletedIntensity.uniform_bound C ε hε
  obtain ⟨NV, _hNV, hv⟩ := PositionalOriginalCovariance.uniform_bound C ε hε
  obtain ⟨NC, _hNC, hc⟩ := PositionalDeletedCountCumulant.uniform_bound C ε hε
  obtain ⟨_B, _hB, NP, _hNP, hp⟩ := PositionalBackgroundMoments.uniform_bound 0 C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NS + NF + NI + NV + NC + NP + NA, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  have hfield := hf N (by omega) L hband
  have hfactor : 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  have hsum := add_le_add hfield.1 hfield.2
  have he : (N : ℝ) ^ (-4 / 5 + ε / 2) + (N : ℝ) ^ (-4 / 5 + ε / 2) =
      2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by ring
  rw [he] at hsum
  exact ⟨(hp N (by omega) L hband (8 * (L + 1) : ℕ)).1, hsum.trans hfactor, hi N (by omega) L hband (8 * (L + 1) : ℕ),
    hv N (by omega) L hband, hc N (by omega) L hband,
    hs N (by omega) L hband (8 * (L + 1) : ℕ)⟩

end PaperP1.PositionalErasureTheorem
