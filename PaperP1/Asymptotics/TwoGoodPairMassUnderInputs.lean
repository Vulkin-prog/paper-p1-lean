module

public import PaperP1.Asymptotics.PrivatePairInteractionMassUnderInputs
public import PaperP1.Model.HomogeneousEdgeInteractions
public import PaperP1.Model.RawGoodPopulation

/-! # The complete two-raw-good-edge homogeneous estimate in companion T1.12(3)

The interaction error has the stronger exponent 41/30. All source cutoffs,
affine-incompatible raw pairs and literal separated unions are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoGoodPairMassUnderInputs

open Finset PaperP1.Model PaperP1.HomogeneousRunMass PaperP1.HomogeneousChannelMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Parameters where
  sourceDegree : ℕ
  generalSize : ℕ
  ordinarySize : ℕ
  typeCap : ℕ

structure Hypotheses (p : Parameters) (b : ℕ) : Prop where
  sourceCover : UniformSourceSurfaceCover.UniformCover p.generalSize
    (AsymmetricComponentHostCount.sizeCap (4 * b) (1 / 12)) p.sourceDegree
  ordinaryCover : UniformOrdinarySurfaceCover.UniformCover p.ordinarySize (p.typeCap + 1)
  sourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.sourceDegree + 2).choose 2 + p.generalSize) M
  ordinaryCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.ordinarySize + 3) M

theorem uniform_channel (a b c d : ℕ) (ha : 0 < a) (hab : a < b) (hint : b < 2 * a) (hcop : a.Coprime b)
    (hc : 0 < c) (hcd : c < d) (hint' : d < 2 * c) (hcop' : c.Coprime d) (hdb : d ≤ b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H₁ H₂ : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        HomogeneousEdgeInteractions.mass L (PrivateChannelActivity.pairs N H₁ a b L)
          (PrivateChannelActivity.pairs N H₂ c d L) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, hu⟩ := PrivatePairInteractionMassUnderInputs.uniform_bound
    a b c d ha hab hint hcop hc hcd hint' hcop' hdb C ε hε
  obtain ⟨NG, hg⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b + c + d : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨⟨Ds, kg, ko, K⟩, ?_⟩
  intro hgeo
  obtain ⟨NU, _hNU, hU⟩ := hu hgeo.sourceCover hgeo.ordinaryCover hgeo.sourceCurves hgeo.ordinaryCurves
  refine ⟨max 10 (max NG NU), by omega, ?_⟩
  intro N hN L H₁ H₂ hcrit
  have hlarge : (a + b + c + d) * (L + 1) < N := by
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using hg N (by omega) L hcrit
  rw [HomogeneousEdgeInteractions.source_mass_eq (by omega) hab hcd
    (by nlinarith only [hlarge, Nat.zero_le ((c + d) * (L + 1))])
    (by nlinarith only [hlarge, Nat.zero_le ((a + b) * (L + 1))])]
  exact hU N (by omega) L H₁ H₂ hcrit

theorem principal_interactions (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        HomogeneousEdgeInteractions.mass L (rawPrincipal N H L) (rawPrincipal N H L) ≤
          (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨p23, h23⟩ := uniform_channel 2 3 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) C (ε / 2) (by positivity)
  obtain ⟨p43, h43⟩ := uniform_channel 3 4 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) C (ε / 2) (by positivity)
  obtain ⟨p44, h44⟩ := uniform_channel 3 4 3 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) C (ε / 2) (by positivity)
  obtain ⟨NF, hF⟩ := HalfCountSchedule.factor_absorption 4 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨N23, _hN23, hu23⟩ := h23 hg23
  obtain ⟨N43, _hN43, hu43⟩ := h43 hg43
  obtain ⟨N44, _hN44, hu44⟩ := h44 hg44
  refine ⟨max 10 (max NF (max N23 (max N43 N44))), by omega, ?_⟩
  intro N hN L H hcrit
  let E := PrivateChannelActivity.pairs N H 2 3 L
  let F := PrivateChannelActivity.pairs N H 3 4 L
  have he := hu23 N (by omega) L H H hcrit
  have hef := hu43 N (by omega) L H H hcrit
  have hf := hu44 N (by omega) L H H hcrit
  have hfirst := HomogeneousEdgeInteractions.union_left L E F (E ∪ F)
  have hleft := HomogeneousEdgeInteractions.union_right L E E F
  have hright := HomogeneousEdgeInteractions.union_right L F E F
  rw [HomogeneousEdgeInteractions.symmetric L E F] at hleft
  have htotal : HomogeneousEdgeInteractions.mass L (rawPrincipal N H L) (rawPrincipal N H L) ≤
      4 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    change HomogeneousEdgeInteractions.mass L (E ∪ F) (E ∪ F) ≤ _
    linarith only [hfirst, hleft, hright, he, hef, hf]
  exact htotal.trans (by simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hF N (by omega))

theorem uniform_homogeneous_second (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        HomogeneousEdgeInteractions.second L (rawPrincipal N H L) ≤
          PrimitiveNominalMass.mass (rawPrincipal N H L) L ^ 2 + (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨p23, p43, p44, hu⟩ := principal_interactions C ε hε
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨N₀, hN₀, hU⟩ := hu hg23 hg43 hg44
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hcrit
  have heq : (∑ e ∈ rawPrincipal N H L, probability L e) = PrimitiveNominalMass.mass (rawPrincipal N H L) L :=
    sum_congr rfl (fun e he ↦ regular_weight (raw_principal_regular (by omega) he))
  have hh := HomogeneousEdgeInteractions.finite_upper L (rawPrincipal N H L)
  rw [heq] at hh
  exact hh.trans (add_le_add le_rfl (hU N hN L H hcrit))

def nominalSecond (N H L : ℕ) : ℝ :=
  ∑ p ∈ ((rawPrincipal N H L) ×ˢ (rawPrincipal N H L)).filter
    (fun p ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)),
      PrimitiveNominalMass.weight L (p.1 ∪ p.2)

theorem nominal_second_eq {N H L : ℕ} (hN : 2 ≤ N) :
    nominalSecond N H L = HomogeneousEdgeInteractions.second L (rawPrincipal N H L) := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨he, hf⟩ := mem_product.mp (mem_filter.mp hp).1
  exact (regular_weight (union_subset (raw_principal_regular hN he) (raw_principal_regular hN hf))).symm

theorem companion_T1_12_two_pairs (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        nominalSecond N H L ≤ K * ((N : ℝ) ^ (-5 / 4 + ε) + ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2) := by
  obtain ⟨p23, p43, p44, hu⟩ := uniform_homogeneous_second C ε hε
  obtain ⟨A, hA, NA, _hNA, hmass⟩ := uniform_principal_upper C
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨NU, _hNU, hU⟩ := hu hg23 hg43 hg44
  refine ⟨A ^ 2 + 1, by positivity, max 10 (max NA NU), by omega, ?_⟩
  intro N hN L H hcrit
  rw [nominal_second_eq (by omega)]
  have hnon : 0 ≤ PrimitiveNominalMass.mass (rawPrincipal N H L) L :=
    sum_nonneg (fun e _ ↦ PrimitiveNominalMass.weight_nonneg L e)
  have hsq := pow_le_pow_left₀ hnon (hmass N (by omega) L H hcrit) 2
  have hp : (N : ℝ) ^ (-41 / 30 + ε) ≤ (N : ℝ) ^ (-5 / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have hU' := hU N (by omega) L H hcrit
  have hpos : 0 ≤ (N : ℝ) ^ (-5 / 4 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith only [hU', hsq, hp, hpos, sq_nonneg ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)),
    mul_nonneg (sq_nonneg A) hpos]

theorem companion_T1_12_two_pairs_original (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑ p ∈ ((RawGoodPopulation.edges (H : ℝ) N L) ×ˢ (RawGoodPopulation.edges (H : ℝ) N L)).filter
          (fun p ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)),
          PrimitiveNominalMass.weight L (p.1 ∪ p.2)) ≤
            K * ((N : ℝ) ^ (-5 / 4 + ε) + ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2) := by
  obtain ⟨p23, p43, p44, hu⟩ := companion_T1_12_two_pairs C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨K, hK, NU, _hNU, hU⟩ := hu hg23 hg43 hg44
  refine ⟨K, hK, max 10 (max NG NU), by omega, ?_⟩
  intro N hN L H hcrit
  rw [RawGoodPopulation.edges_eq_channels (H := H) (by omega) (hg N (by omega) L hcrit).2]
  exact hU N (by omega) L H hcrit

end PaperP1.TwoGoodPairMassUnderInputs
