module

public import PaperP1.Asymptotics.SourcePairCloseWeight

/-! # The literal separated signed arithmetic profile in article Theorem 3.3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSeparatedSourceProfileUnderInputs

open Finset PaperP1.Model PaperP1.SourcePairAffineWeight

theorem article_3_3_signed (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, SourcePairAffineWeight.signedWeight p.1 p.2 L) -
          SignedSourceProfileUnderInputs.mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hall⟩ := SignedSourceProfileUnderInputs.uniform_all_ordered C (ε / 2) (by positivity)
  obtain ⟨Nc, _hNc, hc⟩ := SourcePairCloseWeight.uniform_abs C (ε / 2) (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (6 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨Na, _hNa, ha⟩ := hall hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max Na (max Nc Nf)), by omega, ?_⟩
  intro N hN L hcrit
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpart := PairSeparation.sum_partition (dyadicBlock N) L (fun p ↦ signedWeight p.1 p.2 L)
  have heq : (∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, signedWeight p.1 p.2 L) -
      SignedSourceProfileUnderInputs.mainTerm N L =
      ((∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), signedWeight p.1 p.2 L) -
        SignedSourceProfileUnderInputs.mainTerm N L) -
          ∑ p ∈ PairSeparation.closeHosts (dyadicBlock N) L, signedWeight p.1 p.2 L := by
    linarith only [hpart]
  have htriangle : |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, signedWeight p.1 p.2 L) -
      SignedSourceProfileUnderInputs.mainTerm N L| ≤
      |(∑ p ∈ OrderedPairTuples.pairs (dyadicBlock N), signedWeight p.1 p.2 L) -
        SignedSourceProfileUnderInputs.mainTerm N L| +
          ∑ p ∈ PairSeparation.closeHosts (dyadicBlock N) L, |signedWeight p.1 p.2 L| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _))
  have hall' := ha N (by omega) L hcrit
  have hclose := hc N (by omega) L hcrit
  have hcompare : (N : ℝ) ^ (1 + ε / 2) ≤ (N : ℝ) ^ (6 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hfactor : 2 * (N : ℝ) ^ (6 / 5 + ε / 2) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [htriangle, hall', hclose, hcompare, hfactor]

end PaperP1.SignedSeparatedSourceProfileUnderInputs
