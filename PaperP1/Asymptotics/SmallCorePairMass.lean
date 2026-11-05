module

public import PaperP1.Model.SmallCorePairDeficit
public import PaperP1.Asymptotics.AllPairDeficit

/-! # The whole size-two chosen-core branch has the proved pair-deficit rate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCorePairMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_pair_source (v C ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ D ∈ (SmallCoreFamilyCover.cores G L).filter (fun D ↦ D.card = 2),
          v ^ D.card * infiniteJointMoment L D *
            IndependentExtensionDeficit.deficit G D (FixedPairExtensions.sourceSpace D L) L v) ≤
          (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NP, _hNP, hpair⟩ := AllPairDeficit.article_15_9 v C (ε / 2) hv (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * v ^ 2)
    (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hpairG := (AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L v hv.le).trans
    (hpair N (by omega) L hband)
  calc
    _ ≤ 2 * v ^ 2 * AllPairExtensionDeficit.deficit G L v :=
      SmallCorePairDeficit.pair_bound G L hL v hv.le
    _ ≤ 2 * v ^ 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hpairG (by positivity)
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_pair_families (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ ConnectedWindowFamilies.Connected L I ∧ 256 < I.card ∧
          (ChosenRelationCore.core L I).card = 2) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NP, _hNP, hpair⟩ := AllPairDeficit.article_15_9
    (512 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * (512 * u) ^ 2)
    (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hpairG := (AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L
    (512 * u) (by positivity)).trans (hpair N (by omega) L hband)
  calc
    _ ≤ 2 * (512 * u) ^ 2 * AllPairExtensionDeficit.deficit G L (512 * u) :=
      SmallCorePairDeficit.pair_family_bound G L hL u hu.le F hF
    _ ≤ 2 * (512 * u) ^ 2 * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hpairG (by positivity)
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SmallCorePairMass
