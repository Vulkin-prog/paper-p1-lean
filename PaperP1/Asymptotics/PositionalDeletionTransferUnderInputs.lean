module

public import PaperP1.Model.PositionalDeletedFields
public import PaperP1.Probability.PositionalDeletionWeightedContraction
public import PaperP1.Asymptotics.PositionalWeightedApproximationUnderInputs

/-! # The actual deleted fields inherit moments and the full weighted comparison

The target here is the SAME deletion applied to the compound field. Its further
comparison to the independent single-arrival field remains a separate step.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletionTransferUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalDeletedFields PaperP1.PositionalDeletionKernels
  PaperP1.RetainedComponentActivityUnderInputs

theorem uniform_original_moments (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ E : Finset (Finset ℕ),
      (Summable (fun v ↦ coeff v (onceLaw E G L) * (1 + (totalCount v : ℝ)) ^ r) ∧
        (∑' v, coeff v (onceLaw E G L) * (1 + (totalCount v : ℝ)) ^ r) ≤ (N : ℝ) ^ ε) ∧
      (Summable (fun v ↦ coeff v (isolatedLaw E G L) * (1 + (totalCount v : ℝ)) ^ r) ∧
        (∑' v, coeff v (isolatedLaw E G L) * (1 + (totalCount v : ℝ)) ^ r) ≤ (N : ℝ) ^ ε) := by
  obtain ⟨N₀, hN₀, h⟩ := PositionalMomentBounds.uniform_original r C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG E
  have hh := h N hN L hband G hG
  have hs : Summable (fun v ↦ coeff v (original G L) * (1 + (totalCount v : ℝ)) ^ r) := by
    simpa only [original, coeff_ofFinite] using hh.1
  have hm : (∑' v, coeff v (original G L) * (1 + (totalCount v : ℝ)) ^ r) ≤ (N : ℝ) ^ ε := by
    simpa only [original, coeff_ofFinite] using hh.2
  have ho := once_polynomial_moment_bound E _ (original_isProbability G L).1 r hs
  have hi := isolated_polynomial_moment_bound E _ (original_isProbability G L).1 r hs
  exact ⟨⟨ho.1, ho.2.trans hm⟩, ⟨hi.1, hi.2.trans hm⟩⟩

theorem uniform_weighted_comparison (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 128) (1 / 12)) → ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ E : Finset (Finset ℕ),
        let T := PositionalCompoundPoisson.target (dyadicBlock N)
          (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
        (Summable (fun v : Configuration ℕ ↦ (1 + (totalCount v : ℝ)) ^ j *
          |coeff v (onceLaw E (dyadicBlock N) L) - coeff v (once E T)|) ∧
          (∑' v : Configuration ℕ, (1 + (totalCount v : ℝ)) ^ j *
            |coeff v (onceLaw E (dyadicBlock N) L) - coeff v (once E T)|) ≤
              (N : ℝ) ^ (-4 / 5 + ε)) ∧
        (Summable (fun v : Configuration ℕ ↦ (1 + (totalCount v : ℝ)) ^ j *
          |coeff v (isolatedLaw E (dyadicBlock N) L) - coeff v (isolated E T)|) ∧
          (∑' v : Configuration ℕ, (1 + (totalCount v : ℝ)) ^ j *
            |coeff v (isolatedLaw E (dyadicBlock N) L) - coeff v (isolated E T)|) ≤
              (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨p, hp⟩ := PositionalWeightedApproximationUnderInputs.uniform_coefficient_bound C ε hε
  refine ⟨p, ?_⟩
  intro hgeo j
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo j
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband E
  dsimp only
  let A := original (dyadicBlock N) L
  let T := PositionalCompoundPoisson.target (dyadicBlock N)
    (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  have hh := h N hN L hband
  have hs : Summable (fun v : Configuration ℕ ↦ (1 + (totalCount v : ℝ)) ^ j *
      |coeff v A - coeff v T|) := by
    simpa only [A, original, T, coeff_ofFinite] using hh.1
  have hm : (∑' v : Configuration ℕ, (1 + (totalCount v : ℝ)) ^ j *
      |coeff v A - coeff v T|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    simpa only [A, original, T, coeff_ofFinite] using hh.2
  have ho := PositionalDeletionWeightedContraction.once_weighted_contraction E A T j hs
  have hi := PositionalDeletionWeightedContraction.isolated_weighted_contraction E A T j hs
  exact ⟨⟨ho.1, ho.2.trans hm⟩, ⟨hi.1, hi.2.trans hm⟩⟩

end PaperP1.PositionalDeletionTransferUnderInputs
