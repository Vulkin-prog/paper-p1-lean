module

public import PaperP1.Asymptotics.TwoGoodPairMassUnderInputs
public import PaperP1.Asymptotics.PrincipalEdgeSecondMomentLower
public import PaperP1.Model.GoodEdgePositivePalm
public import PaperP1.Model.ActiveEdgeBonferroni
public import PaperP1.Model.OnceAllOriginalCoupling
public import PaperP1.Model.GoodPrincipalPopulation

/-! # The actual positive two-good-edge second factorial moment

Homogeneous interaction mass bounds the original joint sum; independent
effective blocks factor with their actual affine phases. A fixed gap
41/30 > 4/3 gives the uniform relative error in companion T1.17.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoGoodEdgeSecondMomentUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.PrincipalChannelEdges PaperP1.PrincipalEdgeSpaces PaperP1.TwoGoodPairMassUnderInputs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_upper {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 29 * (L + 1) < N) :
    jointSecond N H L ≤ beta N H L ^ 2 +
      HomogeneousEdgeInteractions.mass L (HomogeneousChannelMass.rawPrincipal N H L) (HomogeneousChannelMass.rawPrincipal N H L) := by
  let E := edges N H L
  let q := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L (p.1 ∪ p.2)
  let b := fun p : Finset ℕ × Finset ℕ ↦ infiniteJointMoment L p.1 * infiniteJointMoment L p.2
  let g := fun p : Finset ℕ × Finset ℕ ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) ∧
    HomogeneousEdgeInteractions.space L p.1 ⊓ HomogeneousEdgeInteractions.space L p.2 ≠ ⊥
  have hpoint (p : Finset ℕ × Finset ℕ) (hp : p ∈ E ×ˢ E) :
      (if p.1 ≠ p.2 then q p else 0) ≤ b p + (if g p then HomogeneousRunMass.probability L (p.1 ∪ p.2) else 0) := by
    have hb : 0 ≤ b p := mul_nonneg (infiniteJointMoment_nonneg L p.1) (infiniteJointMoment_nonneg L p.2)
    have hg : 0 ≤ if g p then HomogeneousRunMass.probability L (p.1 ∪ p.2) else 0 := by
      split_ifs
      · exact (HomogeneousRunMass.probability_pos L _).le
      · rfl
    by_cases hne : p.1 ≠ p.2
    · rw [ite_eq_left hne]
      by_cases hi : HomogeneousEdgeInteractions.space L p.1 ⊓ HomogeneousEdgeInteractions.space L p.2 = ⊥
      · have hspaces : Disjoint (space L p.1) (space L p.2) := disjoint_iff.mpr hi
        have heq : q p = b p := joint_factor hN hL hlarge (mem_product.mp hp).1 (mem_product.mp hp).2 hspaces
        linarith only [heq, hg]
      · by_cases hq : 0 < q p
        · have hsep := GoodEdgePositivePalm.separated_of_positive_joint L hL (p.1 ∪ p.2) hq
          rw [ite_eq_left (show g p from ⟨hne, hsep, hi⟩)]
          have hh := HomogeneousRunMass.actual_joint_le L hL (p.1 ∪ p.2)
          linarith only [hh, hb]
        · have hh := le_of_not_gt hq
          linarith only [hh, hb, hg]
    · rw [ite_eq_right hne]
      linarith only [hb, hg]
  have hbeta : (∑ p ∈ E ×ˢ E, b p) = beta N H L ^ 2 := by
    rw [sum_product, ← sum_mul_sum, pow_two]
    rfl
  have hraw : E ⊆ HomogeneousChannelMass.rawPrincipal N H L := by
    intro e he
    rcases mem_union.mp he with h23 | h34
    · exact mem_union_left _ (mem_filter.mp h23).1
    · exact mem_union_right _ (mem_filter.mp h34).1
  calc
    _ ≤ (∑ p ∈ E ×ˢ E, b p) + HomogeneousEdgeInteractions.mass L E E := by
      rw [jointSecond, factorialPairs, HomogeneousEdgeInteractions.mass,
        HomogeneousEdgeInteractions.pairs, sum_filter, sum_filter, ← sum_add_distrib]
      exact sum_le_sum hpoint
    _ ≤ _ := by rw [hbeta]; exact add_le_add le_rfl (HomogeneousEdgeInteractions.mass_mono L hraw hraw)

theorem uniform_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |jointSecond N H L - beta N H L ^ 2| ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨p23, p43, p44, hu⟩ := principal_interactions C ε hε
  obtain ⟨NL, _hNL, hl⟩ := PrincipalEdgeSecondMomentLower.uniform_lower C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨NU, _hNU, hU⟩ := hu hg23 hg43 hg44
  refine ⟨max 10 (max NU (max NL NG)), by omega, ?_⟩
  intro N hN L H hcrit
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hcrit
  have hupper := (finite_upper (H := H) (by omega) hL hlarge).trans (add_le_add le_rfl (hU N (by omega) L H hcrit))
  have hlower := hl N (by omega) L H hcrit
  have hp : (N : ℝ) ^ (-7 / 3 + ε) ≤ (N : ℝ) ^ (-41 / 30 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  exact abs_le.mpr ⟨by linarith only [hlower, hp], by linarith only [hupper]⟩

theorem companion_T1_17 (C : ℝ) (D : ℕ) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, 10 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L H : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        (let M := ∫ ω, (ActiveEdgeObservables.value (edges N H L) L ω ^ 2 - ActiveEdgeObservables.value (edges N H L) L ω)
          ∂infiniteRademacherMeasure
        |M - beta N H L ^ 2| ≤ δ * beta N H L ^ 2 ∧
        M ≤ K * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 ∧
        0 ≤ beta N H L - ActiveEdgeObservables.probability (edges N H L) L ∧
        beta N H L - ActiveEdgeObservables.probability (edges N H L) L ≤ M / 2) := by
  obtain ⟨p23, p43, p44, hu⟩ := uniform_error C (1 / 60) (by norm_num)
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨_c', A, _hc', hA, NA, _hNA, ha⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨NU, _hNU, hU⟩ := hu hg23 hg43 hg44
  refine ⟨2 * A ^ 2, by positivity, ?_⟩
  intro δ hδ
  let e := min δ 1
  have he : 0 < e := lt_min hδ (by norm_num)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / (e * c)) (-27 / 20) (1 / 60) (by norm_num)
  refine ⟨max 10 (max NU (max NB (max NA (max NG NF)))), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  have hbeta := hb N (by omega) L H hcrit hcut hH
  have hfactor : (N : ℝ) ^ (-27 / 20 : ℝ) / (e * c) ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have hh := hf N (by omega)
    rw [show (-27 / 20 : ℝ) + 1 / 60 = -4 / 3 by norm_num] at hh
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hh
  have herr : (N : ℝ) ^ (-27 / 20 : ℝ) ≤ e * beta N H L ^ 2 := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < e * c)).mp hfactor
    have hh' := mul_le_mul_of_nonneg_left hbeta he.le
    nlinarith only [hh, hh']
  have herror := hU N (by omega) L H hcrit
  rw [show (-41 / 30 : ℝ) + 1 / 60 = -27 / 20 by norm_num] at herror
  have hrel : |jointSecond N H L - beta N H L ^ 2| ≤ e * beta N H L ^ 2 := herror.trans herr
  have heδ : e ≤ δ := min_le_left _ _
  have he1 : e ≤ 1 := min_le_right _ _
  have hupper : jointSecond N H L ≤ 2 * beta N H L ^ 2 := by
    have hh := (abs_le.mp hrel).2
    have hh' := mul_le_mul_of_nonneg_right he1 (sq_nonneg (beta N H L))
    nlinarith only [hh, hh']
  have hsq := pow_le_pow_left₀ (beta_nonneg N H L) (ha N (by omega) L H hcrit hcut hH).2 2
  have hgeom := hg N (by omega) L hcrit
  have hBon := (ActiveEdgeBonferroni.principal_mean_and_union (H := H) (by omega) hgeom.2).2
  have hcutoff := PrincipalChannelEdges.subset_pairs (H := H) (by omega : 2 ≤ N) hgeom.2
  have hcut' : ∀ e ∈ edges N H L, ∀ x ∈ e, x + L ≤ dyadicCutoff N L := fun e he' x hx ↦
    CountObservables.dyadic_subset_cutoff (mem_powersetCard.mp (hcutoff he')).1 x hx
  have hfac : ActiveEdgeBonferroni.factorialSecond (edges N H L) L = jointSecond N H L := by
    rw [OnceAllOriginalCoupling.factorialSecond_eq_joint (edges N H L) hcut']
    rfl
  rw [hfac] at hBon
  rw [PrincipalEdgeSecondMomentLower.actual_second_eq (H := H) (by omega) hgeom.2]
  refine ⟨hrel.trans (mul_le_mul_of_nonneg_right heδ (sq_nonneg _)), ?_, hBon.1, hBon.2⟩
  nlinarith only [hupper, hsq]

theorem companion_T1_17_original (C : ℝ) (D : ℕ) :
    ∃ p23 p43 p44 : Parameters, Hypotheses p23 3 → Hypotheses p43 4 → Hypotheses p44 4 →
      ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, 10 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L H : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        |OnceAllOriginalCoupling.second (H : ℝ) N L - RetainedReferenceTheorem.beta (H : ℝ) N L ^ 2| ≤
          δ * RetainedReferenceTheorem.beta (H : ℝ) N L ^ 2 ∧
        OnceAllOriginalCoupling.second (H : ℝ) N L ≤ K * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 ∧
        0 ≤ OnceAllOriginalCoupling.correction (H : ℝ) N L ∧
        OnceAllOriginalCoupling.correction (H : ℝ) N L ≤ OnceAllOriginalCoupling.second (H : ℝ) N L / 2 := by
  obtain ⟨p23, p43, p44, hu⟩ := companion_T1_17 C D
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨p23, p43, p44, ?_⟩
  intro hg23 hg43 hg44
  obtain ⟨K, hK, hU⟩ := hu hg23 hg43 hg44
  refine ⟨K, hK, ?_⟩
  intro δ hδ
  obtain ⟨NU, _hNU, hU⟩ := hU δ hδ
  refine ⟨max 10 (max NG NU), by omega, ?_⟩
  intro N hN L H hcrit hcut hH
  have hlarge := (hg N (by omega) L hcrit).2
  have hh := hU N (by omega) L H hcrit hcut hH
  rw [PrincipalEdgeSecondMomentLower.actual_second_eq (H := H) (by omega) hlarge] at hh
  rw [GoodPrincipalPopulation.second_eq (H := H) (by omega) hlarge,
    GoodPrincipalPopulation.beta_eq (H := H) (by omega) hlarge]
  refine ⟨hh.1, hh.2.1, ?_⟩
  unfold OnceAllOriginalCoupling.correction
  rw [GoodPrincipalPopulation.good_eq_principal (H := H) (by omega) hlarge,
    GoodPrincipalPopulation.beta_eq (H := H) (by omega) hlarge]
  exact hh.2.2

end PaperP1.TwoGoodEdgeSecondMomentUnderInputs
