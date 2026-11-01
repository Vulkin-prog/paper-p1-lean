module

public import PaperP1.Model.LocalBlockBoundarySharp
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Asymptotics.SaturationDegrees

/-! # Companion T19.2: the entire exact local-block description in every critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlocksTheorem

open Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.LocalBlockBoundary
  PaperP1.LocalBlockMass PaperP1.LocalBlockGeometry PaperP1.LocalBlockBoundaryMass
  PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RegularStarts
  PaperP1.CountObservables PaperP1.Probability PaperP1.WindowRelationCode

def BlockConclusion (N L : ℕ) (S : Finset ℕ) : Prop :=
  (block N L S).Nonempty ∧ block N L S = fullBlock L S ∩ dyadicBlock N ∧
    (∀ x ∈ block N L S, infiniteMarginal x L = if x = first S + 1 then 0 else 2 * (2 ^ L : ℝ)⁻¹) ∧
    restrictedCountLaw N L (block N L S) = bernoulli (blockParameter N L S) ∧
    (∀ ω : InfiniteRademacher.InfiniteSample, infiniteStartCount (block N L S) L ω ≤ 1) ∧
    (fullBlock L S).card = L - (last S - first S) + 1 ∧
    (fullBlock L S ⊆ dyadicBlock N →
      (∑ x ∈ block N L S, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹)) =
        (2 ^ L : ℝ)⁻¹ * ((L : ℝ) - (last S - first S : ℕ) - 1))

def Conclusion (N L : ℕ) : Prop :=
  (∀ S ∈ relations N L, BlockConclusion N L S) ∧
    (∀ S ∈ relations N L, ∀ T ∈ relations N L, S ≠ T → Disjoint (block N L S) (block N L T)) ∧
    (relations N L).biUnion (block N L) = irregularStarts N L ∧
    (∀ x ∈ dyadicBlock N, x ∉ irregularStarts N L → infiniteMarginal x L = (2 ^ L : ℝ)⁻¹) ∧
    countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ =
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((block N L S).card - 2 * (endpointCount N S : ℝ)) ∧
    (∑ x ∈ dyadicBlock N, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹|) =
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((block N L S).card : ℝ) ∧
    (truncated N L).card ≤ 2 ∧
    |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1)| ≤
        2 * L * (2 ^ L : ℝ)⁻¹

theorem finite_conclusion {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hNL : L + 1 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    Conclusion N L := by
  refine ⟨?_, ?_, blocks_cover_irregular hN, ?_, mean_discrepancy hN hL hrank,
    absolute_discrepancy hN hL hrank, truncated_card_le_two hN hNL hrank, mean_full_block_error hN hL hNL hrank⟩
  · intro S hS
    exact ⟨block_nonempty hS,
      block_eq_interval hN S ((mem_relations N L S).mp hS).1.1 (last_ge_length hNL hS),
      fun _ hx ↦ block_marginal hN hL hrank hS hx, block_law hN hL hrank hS,
      infiniteCount_le_one ((mem_relations N L S).mp hS).1, fullBlock_card hN hNL hS,
      fun hfull ↦ full_block_contribution hN hL hNL hrank hS hfull⟩
  · exact fun _ hS _ hT hne ↦ blocks_disjoint hN hrank hS hT hne
  · exact fun _ hx hout ↦ outside_marginal hN hL hx hout

theorem finite_conditions (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 ≤ N ∧ 0 < L ∧ L + 1 ≤ N ∧
        ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1 := by
  obtain ⟨Nfinite, hfinite⟩ := PaperP1.SaturationDegrees.finite_conditions C 2 (by norm_num)
  obtain ⟨Nrank, hrank⟩ := PaperP1.RegularSetAsymptotic.dyadic_critical_relation_rank_le_one C
  obtain ⟨Npoly, hpoly⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    PaperP1.CriticalBandScale.upperScale PaperP1.CriticalBandScale.upperScale_pos.le 2 1 1 (by norm_num)
  refine ⟨max Nfinite (max Nrank Npoly), ?_⟩
  intro N hN L hL
  obtain ⟨hN10, hB, _, _, hwidth⟩ := hfinite N (by omega) L hL
  have hpolyN := hpoly N (by omega) L hwidth
  have hwidthN : 2 * (L + 1 : ℝ) ≤ N := by
    simpa only [pow_one, Real.rpow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (L + 1 : ℝ))] using hpolyN
  have hwidthNat : 2 * (L + 1) ≤ N := by exact_mod_cast hwidthN
  exact ⟨by omega, by omega, by omega, hrank N (by omega) L hL⟩

/-- The original local-block proposition, with one threshold before every critical length. -/
theorem companion_T19_2 (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C → Conclusion N L := by
  obtain ⟨N₀, hN₀⟩ := finite_conditions C
  refine ⟨N₀, ?_⟩
  intro N hN L hL
  obtain ⟨hN2, hLpos, hNL, hrank⟩ := hN₀ N hN L hL
  exact finite_conclusion hN2 hLpos hNL hrank

theorem boundary_improvement_uniform (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ -
        (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((L : ℝ) - (last S - first S : ℕ) - 1)| ≤
          2 * ((L : ℝ) - 1) * (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨N₀, hN₀⟩ := finite_conditions C
  refine ⟨N₀, ?_⟩
  intro N hN L hL
  obtain ⟨hN2, hLpos, hNL, hrank⟩ := hN₀ N hN L hL
  exact PaperP1.LocalBlockBoundarySharp.mean_full_block_error_sharp hN2 hLpos hNL hrank

end PaperP1.LocalBlocksTheorem
