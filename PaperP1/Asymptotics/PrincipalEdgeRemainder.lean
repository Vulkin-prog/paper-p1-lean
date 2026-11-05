module

public import PaperP1.Asymptotics.PairProfiles
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase
public import PaperP1.Combinatorics.PairSubfamilyWeights

/-! # Actual ordered covariance away from the principal edges without unproved geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeRemainder

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability
  PaperP1.Model.InfiniteRademacher

theorem regular_nominal_coefficient {N L x y : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hxy : x ≠ y)
    (hx : x ∈ RegularStarts.regularStarts N L) (hy : y ∈ RegularStarts.regularStarts N L) :
    infiniteCenteredCoefficient L {x, y} =
      ∫ ω, ((indicatorValue (infiniteStartIndicator x L ω) : ℝ) - (2 ^ L : ℝ)⁻¹) *
        ((indicatorValue (infiniteStartIndicator y L ω) : ℝ) - (2 ^ L : ℝ)⁻¹) ∂infiniteRademacherMeasure := by
  classical
  have hxpos : 0 < x := by have h := (mem_Ico.mp (RegularStarts.mem_regularStarts.mp hx).1).1; omega
  have hypos : 0 < y := by have h := (mem_Ico.mp (RegularStarts.mem_regularStarts.mp hy).1).1; omega
  simp only [infiniteCenteredCoefficient, prod_pair hxy, RegularStarts.marginal_on_regular hxpos hL hx,
    RegularStarts.marginal_on_regular hypos hL hy]

theorem uniform_remainder (C ε : ℝ) (Hmult : ℕ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ Hmult * (L + 1) →
        (CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L) ≤
          (N : ℝ) ^ (-4 / 5 + ε) ∧
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
          (∑ p ∈ PairSubfamilyWeights.hosts G (G.powersetCard 2 \ PrincipalChannelEdges.edges N H L),
            |infiniteCenteredCoefficient L {p.1, p.2}|) ≤ (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨Np, _hNp, hp⟩ :=
    PairProfiles.uniform_profiles C (ε / 2) Hmult (by positivity)
  obtain ⟨Na, _hNa, ha⟩ := PairActivityCumulantGapAsymptotic.uniform_gap C (ε / 2) (by positivity)
  obtain ⟨Nb, _hNb, hb⟩ := PrincipalChannelEdgesPhase.uniform_activity_gap C (ε / 2) (by positivity)
  obtain ⟨Ng, _hNg, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 6 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Np (max Na (max Nb (max Ng Nf)))), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  classical
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge := (hg N (by omega) L hcrit).2
  have hκ := (hp N (by omega) L H hcrit hcut hH).1
  have hgap := (ha N (by omega) L hcrit (dyadicBlock N) (subset_refl _)).2
  have hβ := (hb N (by omega) L H hcrit).2
  have hcompare : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
  have hpartition := sum_sdiff (f := fun e ↦ |infiniteCenteredCoefficient L e|)
    (PrincipalChannelEdges.subset_pairs (H := H) (by omega : 2 ≤ N) hlarge)
  change CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L) +
    CompatibleActivitySplit.absolute L (PrincipalChannelEdges.edges N H L) =
      CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) at hpartition
  have hpow : 0 ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hoff : CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L) ≤
      3 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    have hκupper := (abs_le.mp hκ).2
    linarith only [hpartition, hgap, hβ, hκupper, hcompare, hpow]
  have hfactor : 6 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  constructor
  · exact hoff.trans ((by nlinarith only [hpow] :
      3 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ 6 * (N : ℝ) ^ (-4 / 5 + ε / 2)).trans hfactor)
  · intro G hG
    let F := G.powersetCard 2 \ PrincipalChannelEdges.edges N H L
    have hsub : F ⊆ (dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L := by
      intro e he
      obtain ⟨heG, hnot⟩ := mem_sdiff.mp he
      obtain ⟨heG, hecard⟩ := mem_powersetCard.mp heG
      exact mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨heG.trans hG, hecard⟩, hnot⟩
    have hmono : CompatibleActivitySplit.absolute L F ≤
        CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ abs_nonneg _)
    have hsum := PairSubfamilyWeights.weighted_sum G F sdiff_subset (fun e ↦ |infiniteCenteredCoefficient L e|)
    change (∑ p ∈ PairSubfamilyWeights.hosts G F, |infiniteCenteredCoefficient L {p.1, p.2}|) ≤ _
    rw [hsum]
    change 2 * CompatibleActivitySplit.absolute L F ≤ _
    exact (mul_le_mul_of_nonneg_left (hmono.trans hoff) (by norm_num : (0 : ℝ) ≤ 2)).trans
      ((le_of_eq (by ring) : 2 * (3 * (N : ℝ) ^ (-4 / 5 + ε / 2)) ≤ 6 * (N : ℝ) ^ (-4 / 5 + ε / 2)).trans hfactor)

theorem uniform_nominal_remainder (C ε : ℝ) (Hmult : ℕ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ Hmult * (L + 1) →
        (∑ p ∈ PairSubfamilyWeights.hosts (RegularStarts.regularStarts N L)
          ((RegularStarts.regularStarts N L).powersetCard 2 \ PrincipalChannelEdges.edges N H L),
          |∫ ω, ((indicatorValue (infiniteStartIndicator p.1 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹) *
            ((indicatorValue (infiniteStartIndicator p.2 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹)
            ∂infiniteRademacherMeasure|) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨Nr, _hNr, hr⟩ := uniform_remainder C ε Hmult hε
  obtain ⟨Ng, _hNg, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 2 (max Nr Ng), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  have hL := (hg N (by omega) L hcrit).1
  have hsum := (hr N (by omega) L H hcrit hcut hH).2
    (RegularStarts.regularStarts N L) (RegularStarts.regularStarts_subset N L)
  convert hsum using 1
  apply sum_congr rfl
  intro p hp
  have hpdata := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp
  rw [regular_nominal_coefficient (by omega) hL hpdata.2.2.1 hpdata.1 hpdata.2.1]

theorem uniform_edge_input (C ε : ℝ) (Hmult : ℕ) (hε : 0 < ε) :
      ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ Hmult * (L + 1) →
        ((PrincipalChannelEdges.edges N H L).card ≤ 26 * (L + 1) * N ∧
        c * L * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ PrincipalChannelEdges.beta N H L ∧
        PrincipalChannelEdges.beta N H L ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) ∧
        |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
          2 * PrincipalChannelEdges.beta N H L| ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        (∑ p ∈ PairSubfamilyWeights.hosts (RegularStarts.regularStarts N L)
          ((RegularStarts.regularStarts N L).powersetCard 2 \ PrincipalChannelEdges.edges N H L),
          |∫ ω, ((indicatorValue (infiniteStartIndicator p.1 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹) *
            ((indicatorValue (infiniteStartIndicator p.2 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹)
            ∂infiniteRademacherMeasure|) ≤ (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨Nr, _hNr, hr⟩ := uniform_remainder C (ε / 2) Hmult (by positivity)
  obtain ⟨c, K, hc, hK, Nphase, _hNphase, hphase⟩ := PrincipalChannelEdgesPhase.positive_phase C Hmult
  obtain ⟨Na, _hNa, ha⟩ := PairActivityCumulantGapAsymptotic.uniform_gap C (ε / 2) (by positivity)
  obtain ⟨Nb, _hNb, hb⟩ := PrincipalChannelEdgesPhase.uniform_activity_gap C (ε / 2) (by positivity)
  obtain ⟨Nl, _hNl, hl⟩ := PrincipalChannelEdgesPhase.uniform_cumulant_upper_error C (ε / 2) (by positivity)
  obtain ⟨Ng, _hNg, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨c, K, hc, hK, max 2 (max Nr (max Nphase (max Na (max Nb (max Nl (max Ng Nf)))))), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  classical
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hcrit
  have hrem := hr N (by omega) L H hcrit hcut hH
  have hgap := (ha N (by omega) L hcrit (dyadicBlock N) (subset_refl _)).1
  have hβ := (hb N (by omega) L H hcrit).1
  have hlow := hl N (by omega) L H hcrit
  have hpartition := sum_sdiff (f := fun e ↦ |infiniteCenteredCoefficient L e|)
    (PrincipalChannelEdges.subset_pairs (H := H) (by omega : 2 ≤ N) hlarge)
  change CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2 \ PrincipalChannelEdges.edges N H L) +
    CompatibleActivitySplit.absolute L (PrincipalChannelEdges.edges N H L) =
      CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) at hpartition
  have hupper : RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
      2 * PrincipalChannelEdges.beta N H L ≤ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    linarith only [hgap, hβ, hpartition, hrem.1]
  have hcompare : (N : ℝ) ^ (-1 + ε / 2) ≤ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    have hm := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-1 + ε / 2) ≤ -4 / 5 + ε / 2)
    have hp := Real.rpow_nonneg (Nat.cast_nonneg N) (-4 / 5 + ε / 2)
    linarith
  have hfactor : 2 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hκ : |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
      2 * PrincipalChannelEdges.beta N H L| ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    apply abs_le.mpr
    exact ⟨by linarith only [hlow, hcompare, hfactor], hupper.trans hfactor⟩
  obtain ⟨hphaselo, hphasehi⟩ := hphase N (by omega) L H hcrit hcut hH
  refine ⟨PrincipalChannelEdges.card_bound hNpos, hphaselo, hphasehi, hκ, ?_⟩
  have hsum := hrem.2 (RegularStarts.regularStarts N L) (RegularStarts.regularStarts_subset N L)
  have hnom : (∑ p ∈ PairSubfamilyWeights.hosts (RegularStarts.regularStarts N L)
      ((RegularStarts.regularStarts N L).powersetCard 2 \ PrincipalChannelEdges.edges N H L),
      |∫ ω, ((indicatorValue (infiniteStartIndicator p.1 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹) *
        ((indicatorValue (infiniteStartIndicator p.2 L ω) : ℝ) - (2 ^ L : ℝ)⁻¹)
        ∂infiniteRademacherMeasure|) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    convert hsum using 1
    apply sum_congr rfl
    intro p hp
    have hpdata := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp
    rw [regular_nominal_coefficient (by omega) hL hpdata.2.2.1 hpdata.1 hpdata.2.1]
  exact hnom.trans ((by have hp := Real.rpow_nonneg (Nat.cast_nonneg N) (-4 / 5 + ε / 2); linarith :
    (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ 2 * (N : ℝ) ^ (-4 / 5 + ε / 2)).trans hfactor)

end PaperP1.PrincipalEdgeRemainder
