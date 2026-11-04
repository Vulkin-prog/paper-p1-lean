module

public import PaperP1.Asymptotics.PositionalOriginalDeletionUnderInputs
public import PaperP1.Asymptotics.PositionalDeletedBackgroundMoments

/-! # Every fixed polynomial weight for the actual erased and isolated fields -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalOriginalDeletionWeightedUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalDeletedFields PaperP1.RetainedComponentActivityUnderInputs

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 256) (1 / 12)) → ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
        let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        (Summable (fun v ↦ (1 + (totalCount v : ℝ)) ^ j *
          |coeff v (onceLaw E (dyadicBlock N) L) - coeff v U|) ∧
          (∑' v, (1 + (totalCount v : ℝ)) ^ j *
            |coeff v (onceLaw E (dyadicBlock N) L) - coeff v U|) ≤ (N : ℝ) ^ (-4 / 5 + ε)) ∧
        (Summable (fun v ↦ (1 + (totalCount v : ℝ)) ^ j *
          |coeff v (isolatedLaw E (dyadicBlock N) L) - coeff v U|) ∧
          (∑' v, (1 + (totalCount v : ℝ)) ^ j *
            |coeff v (isolatedLaw E (dyadicBlock N) L) - coeff v U|) ≤ (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨p, hp⟩ := PositionalOriginalDeletionUnderInputs.uniform_norm_bound C (ε / 4) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 4) / 64 = ε / 256 := by ring
  obtain ⟨NN, _hNN, hn⟩ := hp (by simpa only [hscale] using hgeo)
  let A := fun N L ↦ onceLaw (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L) (dyadicBlock N) L
  let B := fun N L ↦ isolatedLaw (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L) (dyadicBlock N) L
  let U := fun N L ↦ PositionalMarkedPairExpansion.background (dyadicBlock N)
    (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  have hNormA : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ‖A N L - U N L‖ ≤ (N : ℝ) ^ (-(4 / 5 : ℝ) + ε / 4) := by
    refine ⟨NN, ?_⟩
    intro N hN L hband
    simpa only [neg_div] using (hn N hN L hband).1
  have hNormB : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ‖B N L - U N L‖ ≤ (N : ℝ) ^ (-(4 / 5 : ℝ) + ε / 4) := by
    refine ⟨NN, ?_⟩
    intro N hN L hband
    simpa only [neg_div] using (hn N hN L hband).2
  have hMomA : ∀ r : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PolynomialWeightedFieldRate.MomentBounds (A N L) (U N L) r ((N : ℝ) ^ δ) := by
    intro r δ hδ
    obtain ⟨NM, _hNM, hm⟩ := PositionalDeletedBackgroundMoments.uniform_bound r C δ hδ
    exact ⟨NM, fun N hN L hband ↦ (hm N hN L hband).1⟩
  have hMomB : ∀ r : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₂ : ℕ, ∀ N ≥ N₂, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PolynomialWeightedFieldRate.MomentBounds (B N L) (U N L) r ((N : ℝ) ^ δ) := by
    intro r δ hδ
    obtain ⟨NM, _hNM, hm⟩ := PositionalDeletedBackgroundMoments.uniform_bound r C δ hδ
    exact ⟨NM, fun N hN L hband ↦ (hm N hN L hband).2⟩
  have hA := PolynomialWeightedFieldRate.uniform_bound A U C (4 / 5) ε hε hNormA hMomA
  have hB := PolynomialWeightedFieldRate.uniform_bound B U C (4 / 5) ε hε hNormB hMomB
  intro j
  obtain ⟨NA, _hNA, ha⟩ := hA j
  obtain ⟨NB, _hNB, hb⟩ := hB j
  refine ⟨10 + NA + NB, by omega, ?_⟩
  intro N hN L hband
  have hh := And.intro (ha N (by omega) L hband) (hb N (by omega) L hband)
  simpa only [A, B, U, neg_div] using hh

end PaperP1.PositionalOriginalDeletionWeightedUnderInputs
