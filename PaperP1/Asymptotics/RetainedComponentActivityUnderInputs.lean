module

public import PaperP1.Asymptotics.RetainedBadPairActivityUnderInputs
public import PaperP1.Asymptotics.GrowingConnectedUnderInputs
public import PaperP1.Asymptotics.FinitePairActivityInputs

/-! # All actual component activities in the literal linear boundary range share one threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedComponentActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedBoundaryPositiveMass

structure Parameters where
  lowOrder : ℕ
  coreOrder : ℕ
  lowConnected : CoarseConnectedParameters.Parameters lowOrder
  lowIncompatible : CoarseConnectedParameters.Parameters lowOrder
  lowPair : FinitePairDeficitInputs.Parameters
  core : CoarseConnectedParameters.Parameters coreOrder
  corePair : FinitePairDeficitInputs.Parameters
  pair : FinitePairDeficitInputs.Parameters
  bad : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  lowConnected : CoarseConnectedParameters.Hypotheses p.lowConnected (ε / 128)
  lowIncompatible : CoarseConnectedParameters.Hypotheses p.lowIncompatible (ε / 512)
  lowPair : FinitePairDeficitInputs.Hypotheses p.lowPair (GeneralGraphHostCount.sizeCap (ε / 524288))
  core : CoarseConnectedParameters.Hypotheses p.core (ε / 128)
  corePair : FinitePairDeficitInputs.Hypotheses p.corePair (GeneralGraphHostCount.sizeCap (ε / 1024))
  pair : FinitePairDeficitInputs.Hypotheses p.pair (GeneralGraphHostCount.sizeCap (1 / 100))
  bad : FinitePairDeficitInputs.Hypotheses p.bad (GeneralGraphHostCount.sizeCap (ε / 128))

theorem uniform_bounds (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ K : ℕ, 4 * K ≤ L →
      badActivity (8 * (L + 1) : ℕ) N L ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      higherActivity N L K ≤ (N : ℝ) ^ (-1 + ε) ∧
      goodActivity (8 * (L + 1) : ℕ) N L + badActivity (8 * (L + 1) : ℕ) N L ≤
        (N : ℝ) ^ (-2 / 3 + ε) := by
  classical
  obtain ⟨sl, sc, _hsl, _hsc, plc, pli, plp, pc, pp, hh⟩ :=
    GrowingConnectedUnderInputs.uniform_linear_range 4 (3 / 2) 2 C ε
      (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε
  obtain ⟨pa, ha⟩ := FinitePairActivityInputs.uniform_pair C (ε / 2) (by positivity)
  obtain ⟨pb, hb⟩ := RetainedBadPairActivityUnderInputs.uniform_bound C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨sl, sc, plc, pli, plp, pc, pp, pa, pb⟩, ?_⟩
  intro hgeo
  obtain ⟨NH, _hNH, hh⟩ := hh hgeo.lowConnected hgeo.lowIncompatible hgeo.lowPair hgeo.core hgeo.corePair
  obtain ⟨NA, _hNA, ha⟩ := ha hgeo.pair
  obtain ⟨NB, _hNB, hb⟩ := hb hgeo.bad
  refine ⟨10 + NH + NA + NB + NG + NF, by omega, ?_⟩
  intro N hN L hband K hK
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  refine ⟨hb N (by omega) L hband, ?_, ?_⟩
  · apply hh N (by omega) L hband K (by norm_num; exact hK)
      (RegularStarts.regularStarts N L) (RegularStarts.regularStarts_subset N L)
      (ActualComponentRemainder.higher (RegularStarts.regularStarts N L) L K (3 / 2))
    intro I hI
    obtain ⟨hIG, hthree, hsize, hconn, hcap⟩ := mem_filter.mp hI
    exact ⟨mem_powerset.mp hIG, hthree, hsize, hconn, hcap⟩
  · rw [← pair_activity_split _ N L (by omega) hL]
    have heq : (∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2, ActualComponentRemainder.weight L 2 e) =
        4 * ∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2, |infiniteCenteredCoefficient L e| := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      have hcard := (mem_powersetCard.mp he).2
      simp only [ActualComponentRemainder.weight, hcard]
      norm_num
    rw [heq]
    calc
      _ ≤ 4 * (N : ℝ) ^ (-2 / 3 + ε / 2) := mul_le_mul_of_nonneg_left
        (ha N (by omega) L hband _ (RegularStarts.regularStarts_subset N L)) (by norm_num)
      _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring

end PaperP1.RetainedComponentActivityUnderInputs
