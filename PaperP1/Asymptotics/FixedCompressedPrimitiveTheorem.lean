module

public import PaperP1.Asymptotics.EffectiveCompressedPrimitiveMass
public import PaperP1.Asymptotics.PairCompressedPrimitiveMass
public import PaperP1.Asymptotics.HomogeneousEffectiveGoodPairExtensions

/-! # All clauses of companion T4.4 with internally proved inputs

The fixed number of further windows is chosen before the threshold. The
two-block clause is separate and retains the distinguished raw source pair.
All effective targets are allowed in the homogeneous majorants; nominal
rank weights are identified with them only on regular original families.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedCompressedPrimitiveTheorem

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SingletonExtensionWeights

theorem companion_T4_4 (t : ℕ) (ht : 2 ≤ t) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ,
      EffectiveCompressedPrimitivePopulation.mass N 2 3 L t ≤ (N : ℝ) ^ (-5 / 3 + ε) ∧
      EffectiveCompressedPrimitivePopulation.mass N 3 4 L t ≤ (N : ℝ) ^ (-7 / 4 + ε) ∧
      (∑ q ∈ EffectiveCompressedPrimitivePopulation.points N 2 3 L t,
        infiniteJointMoment L (PairCompressedPrimitiveFamilies.family q.1 q.2)) ≤ (N : ℝ) ^ (-5 / 3 + ε) ∧
      (∑ q ∈ EffectiveCompressedPrimitivePopulation.points N 3 4 L t,
        infiniteJointMoment L (PairCompressedPrimitiveFamilies.family q.1 q.2)) ≤ (N : ℝ) ^ (-7 / 4 + ε) ∧
      HomogeneousEffectiveGoodPairExtensions.mass N H 2 3 L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
      HomogeneousEffectiveGoodPairExtensions.mass N H 3 4 L ≤ (N : ℝ) ^ (-5 / 4 + ε) ∧
      (∑ p ∈ HomogeneousEffectiveGoodPairExtensions.points N H 2 3 L,
        infiniteJointMoment L (join p)) ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
      (∑ p ∈ HomogeneousEffectiveGoodPairExtensions.points N H 3 4 L,
        infiniteJointMoment L (join p)) ≤ (N : ℝ) ^ (-5 / 4 + ε) := by
  obtain ⟨NT, _hNT, htM⟩ := EffectiveCompressedPrimitiveMass.full_effective_principal_channels t ht C ε hε
  obtain ⟨N23, _hN23, h23⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass
    2 3 (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨N34, _hN34, h34⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass
    3 4 (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NT + N23 + N34 + NG, by omega, ?_⟩
  intro N hN L hband H
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hh := htM N (by omega) L hband
  have hs23 := (h23 N (by omega) L H hband).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [] : -41 / 30 + ε ≤ -4 / 3 + ε))
  have hs34 := (h34 N (by omega) L H hband).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [] : -41 / 30 + ε ≤ -5 / 4 + ε))
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hs23, hs34, ?_, ?_⟩
  · exact (sum_le_sum fun p _ ↦ HomogeneousRunMass.actual_joint_le L hL (join p)).trans hs23
  · exact (sum_le_sum fun p _ ↦ HomogeneousRunMass.actual_joint_le L hL (join p)).trans hs34

end PaperP1.FixedCompressedPrimitiveTheorem
