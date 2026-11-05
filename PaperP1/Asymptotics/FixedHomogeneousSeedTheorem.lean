module

public import PaperP1.Asymptotics.HomogeneousGoodPairExtensions
public import PaperP1.Asymptotics.HomogeneousPairResidual
public import PaperP1.Asymptotics.HomogeneousTwoEdgeScale

/-! # Complete unconditional companion T1.12 for the original homogeneous seed populations

All three clauses share a threshold. The raw-family constant is fixed before
epsilon; affine-incompatible sources remain in the homogeneous population.
The two-edge bound is strengthened to a true fixed constant times the pair scale squared.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHomogeneousSeedTheorem

open Finset PaperP1.Model PaperP1.HomogeneousRunMass PaperP1.HomogeneousChannelMass

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
      HomogeneousGoodPairExtensions.nominalMass N H 2 3 L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
      HomogeneousGoodPairExtensions.nominalMass N H 3 4 L ≤ (N : ℝ) ^ (-5 / 4 + ε) ∧
      TwoGoodPairMass.nominalSecond N H L ≤
        A * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
  obtain ⟨A₁, hA₁, NA, _hNA, ha⟩ := uniform_principal_upper C
  obtain ⟨A₂, hA₂, NB, _hNB, hb⟩ := HomogeneousTwoEdgeScale.uniform_second C
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro ε hε
  obtain ⟨NR, _hNR, hr⟩ := HomogeneousPairResidual.companion_T1_12_pair_residual C ε D hε
  obtain ⟨N23, _hN23, h23⟩ := HomogeneousGoodPairExtensions.companion_T1_12_channel23 C ε hε
  obtain ⟨N34, _hN34, h34⟩ := HomogeneousGoodPairExtensions.companion_T1_12_channel34 C ε hε
  refine ⟨10 + NA + NB + NG + NR + N23 + N34, by omega, ?_⟩
  intro N hN L H hband hcut hH
  have heq : RawGoodPopulation.edges (H : ℝ) N L = rawPrincipal N H L :=
    RawGoodPopulation.edges_eq_channels (H := H) (by omega) (hg N (by omega) L hband).2
  refine ⟨heq, ?_⟩
  intro G hG
  have hB : 0 ≤ (L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ) := by positivity
  have hraw₀ : PrimitiveNominalMass.mass (rawPrincipal N H L) L ≤
      A₁ * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) := by
    simpa only [mul_assoc] using ha N (by omega) L H hband
  have hraw := hraw₀.trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂.le) hB)
  have hsecond : TwoGoodPairMass.nominalSecond N H L ≤
      (A₁ + A₂) * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
    rw [TwoGoodPairMass.nominal_second_eq (by omega : 2 ≤ N)]
    exact (hb N (by omega) L H hband).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₁.le) (sq_nonneg _))
  exact ⟨hr N (by omega) L H hband hcut hH G hG, hraw,
    (h23 N (by omega) L H hband).2, (h34 N (by omega) L H hband).2, hsecond⟩

end PaperP1.FixedHomogeneousSeedTheorem
