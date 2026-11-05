module

public import PaperP1.Diophantine.GeometricBiformPointCount
public import PaperP1.Algebra.ComplexProjectiveIrreducibility
public import PaperP1.Asymptotics.SharpAsymmetricProfileUnderInputs
public import PaperP1.Asymptotics.SharpExpandedAsymmetricProfileUnderInputs

/-! # Corrected sharp profiles under the four geometric properties alone

Both arithmetic biform inputs are supplied by internal checked proofs.
The four explicit surface-cover and curve properties remain ordinary unproved
parameters. The enlarged alignment domains and literal radius-one counterexample
are unchanged.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpProfilesUnderGeometry

open Finset PaperP1.Model PaperP1.ComplexProjectiveIrreducibility

theorem dyadic_profile
    (C ε : ℝ) (Dold Dcut : ℕ) (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg
        (AsymmetricComponentHostCount.sizeCap Dcut (ε / 8)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ dyadicBlock N, ∀ n ∈ old x,
        |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      PaperP1.AsymmetricCoarseProfileUnderInputs.profile N L H Dold old ≤ (N : ℝ) ^ (31 / 24 + ε)) := by
  exact PaperP1.SharpAsymmetricProfileUnderInputs.uniform_profile GeometricBiformPointCount.full_input nongeometric_input
    C ε Dold Dcut hDold hε

theorem expanded_profile
    (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut : ℕ) (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg
        (AsymmetricComponentHostCount.sizeCap Dcut (ε / 8)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x,
        |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      PaperP1.ExpandedAsymmetricCoarseProfileUnderInputs.profile N Q L H Dold old ≤ (N : ℝ) ^ (31 / 24 + ε)) := by
  exact PaperP1.SharpExpandedAsymmetricProfileUnderInputs.uniform_profile GeometricBiformPointCount.full_input nongeometric_input
    Q hQ C ε Dold Dcut hDold hε

end PaperP1.SharpProfilesUnderGeometry
