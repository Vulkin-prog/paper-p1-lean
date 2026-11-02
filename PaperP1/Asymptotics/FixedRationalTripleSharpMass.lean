module

public import PaperP1.Asymptotics.FixedRationalTripleMass
public import PaperP1.Asymptotics.RationalTripleEvenSharpMass

/-! # The sharp rational mass exponent at fixed height needs no private or regular-window filter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedRationalTripleSharpMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ThreeSlopeProgressions PaperP1.ThreeSlopePrivatePopulation

theorem witness_mem_hosts {N L Q t : ℕ} (hN : 10 ≤ N) (hQ : 15 ≤ Q) (ht : t ∈ good N L) :
    centres t ∈ FixedRationalTripleMass.hosts N Q false := by
  classical
  have hd := mem_filter.mp ht
  have htpos := (parameter_bounds hN hd.1).1
  simpa only [RationalTripleEvenSharpMass.extremal_normalization] using FixedRationalTripleMass.mem_hosts_of_source false
    (by decide : 10 < 12) (by decide : 12 < 15) (by decide : 15 < 2 * 10) (by decide)
    hQ htpos (centres_dyadic hN hd.1) (by simp)

theorem witness_families_subset {N L Q : ℕ} (hN : 10 ≤ N) (hQ : 15 ≤ Q) :
    ThreeSlopePositiveActivity.families N L ⊆ FixedRationalTripleMass.unorderedFamilies N Q false := by
  intro T hT
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
  exact mem_image.mpr ⟨centres t, witness_mem_hosts hN hQ ht, rfl⟩

theorem unordered_lower (C : ℝ) (Q : ℕ) (hQ : 15 ≤ Q) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      RationalTripleEvenSharpMass.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        FixedRationalTripleMass.unorderedMass N L Q false := by
  obtain ⟨N₀, hN₀, hu⟩ := RationalTripleEvenSharpMass.witness_joint_lower C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact (hu N hN L hband).trans
    (sum_le_sum_of_subset_of_nonneg (witness_families_subset (by omega) hQ)
      (fun T _ _ ↦ infiniteJointMoment_nonneg L T))

theorem uniform_sharp_mass (C : ℝ) (Q : ℕ) (hQ : 15 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      RationalTripleEvenSharpMass.lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        FixedRationalTripleMass.unorderedMass N L Q false ∧
      FixedRationalTripleMass.unorderedMass N L Q false ≤ FixedRationalTripleMass.mass N L Q false ∧
      FixedRationalTripleMass.mass N L Q false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := unordered_lower C Q hQ
  obtain ⟨NB, _hNB, hb⟩ := FixedRationalTripleMass.uniform_full_mass Q (by omega) C ε hε
  refine ⟨max 1000 (max NA NB), by omega, ?_⟩
  intro N hN L hband
  exact ⟨ha N (by omega) L hband, FixedRationalTripleMass.unordered_mass_le N L Q false,
    hb N (by omega) L hband⟩

end PaperP1.FixedRationalTripleSharpMass
