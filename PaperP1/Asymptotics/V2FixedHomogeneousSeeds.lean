module

public import PaperP1.Asymptotics.FixedHomogeneousSeedTheorem
public import PaperP1.Asymptotics.HomogeneousEffectiveGoodPairExtensions

/-! # The strengthened V2 T1.12 with a common threshold

Regular nominal weights identify with the homogeneous law. Their source/target
population is contained in the already bounded effective population, including
affine-incompatible sources. The two-edge constant still precedes epsilon.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.V2FixedHomogeneousSeeds

open Finset PaperP1.Model PaperP1.HomogeneousRunMass PaperP1.HomogeneousChannelMass

theorem finite_nominal_domination {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b) :
    HomogeneousGoodPairExtensions.nominalMass N H a b L ≤
      HomogeneousEffectiveGoodPairExtensions.mass N H a b L := by
  classical
  rw [HomogeneousGoodPairExtensions.nominal_mass_eq hN ha hab]
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ ↦ (probability_pos L _).le)
  intro p hp
  obtain ⟨hbox, hrest⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  exact mem_filter.mpr ⟨mem_product.mpr ⟨he, RegularStarts.regularStarts_subset N L hz⟩, hrest⟩

theorem companion_T1_12 (C : ℝ) (D : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L H : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      RawGoodPopulation.edges (H : ℝ) N L = rawPrincipal N H L ∧
      ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
      (PrimitiveNominalMass.mass (HomogeneousPairResidual.families N H L G) L ≤
          (N : ℝ) ^ (-4 / 5 + ε) ∧
        (∑ e ∈ HomogeneousPairResidual.families N H L G, probability L e) ≤
          (N : ℝ) ^ (-4 / 5 + ε)) ∧
      PrimitiveNominalMass.mass (rawPrincipal N H L) L ≤
        A * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ∧
      HomogeneousGoodPairExtensions.nominalMass N H 2 3 L ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
      HomogeneousGoodPairExtensions.nominalMass N H 3 4 L ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
      TwoGoodPairMass.nominalSecond N H L ≤
        A * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
  obtain ⟨A, hA, h⟩ := FixedHomogeneousSeedTheorem.companion_T1_12 C D
  refine ⟨A, hA, ?_⟩
  intro ε hε
  obtain ⟨NO, _hNO, ho⟩ := h ε hε
  obtain ⟨N23, _hN23, h23⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass
    2 3 (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨N34, _hN34, h34⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass
    3 4 (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨10 + NO + N23 + N34, by omega, ?_⟩
  intro N hN L H hband hcut hH
  obtain ⟨heq, hG⟩ := ho N (by omega) L H hband hcut hH
  refine ⟨heq, ?_⟩
  intro G hsub
  obtain ⟨hres, hraw, _hold23, _hold34, hsecond⟩ := hG G hsub
  exact ⟨hres, hraw,
    (finite_nominal_domination (by omega) (by decide : 0 < 2) (by decide : 2 < 3)).trans
      (h23 N (by omega) L H hband),
    (finite_nominal_domination (by omega) (by decide : 0 < 3) (by decide : 3 < 4)).trans
      (h34 N (by omega) L H hband), hsecond⟩

end PaperP1.V2FixedHomogeneousSeeds
