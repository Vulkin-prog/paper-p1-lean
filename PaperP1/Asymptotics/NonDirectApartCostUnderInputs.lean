module

public import PaperP1.Model.NonDirectApartPartition
public import PaperP1.Asymptotics.GoodApartPairProductMass
public import PaperP1.Asymptotics.FinitePairActivityInputs

/-! # The literal non-direct apart cost has rate five thirds under finite geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonDirectApartCostUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ pp pw : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (1 / 100)) →
      FinitePairDeficitInputs.Hypotheses pw (GeneralGraphHostCount.sizeCap (ε / 1024)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      DirectPairProductComparison.nonDirectApartCost (dyadicBlock N) L ≤
        (N : ℝ) ^ (-5 / 3 + ε) := by
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Q, _hQ, hpartition⟩ := FinitePairDeficitInputs.partition_inputs δ hδ
  obtain ⟨pw, hpw⟩ := hpartition C δ hδ
  obtain ⟨pp, hpp⟩ := FinitePairActivityInputs.uniform_pair C δ hδ
  obtain ⟨NG, _hNG, hg⟩ := GoodApartPairProductMass.uniform_mass Q C δ hδ
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pp, pw, ?_⟩
  intro hgeoP hgeoW
  obtain ⟨NP, _hNP, hp⟩ := hpp hgeoP
  obtain ⟨NW, _hNW, hw⟩ := hpw (by simpa only [δ, show ε / 8 / 128 = ε / 1024 by ring] using hgeoW)
  refine ⟨max 2 (max NP (max NW (max NG (max NL NF)))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  have hpair := hp N (by omega) L hband (dyadicBlock N) (subset_refl _)
  change CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) ≤
    (N : ℝ) ^ (-2 / 3 + δ) at hpair
  obtain ⟨hweak, hex⟩ := hw N (by omega) L hband
  have hex' := hex.trans (Real.rpow_le_rpow_of_exponent_le hn1 (show -1 + δ ≤ -1 + δ + δ by linarith only [hδ]))
  have hproduct : (N : ℝ) ^ (-2 / 3 + δ) * (N : ℝ) ^ (-1 + δ + δ) ≤
      (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    rw [← Real.rpow_add hn]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hbad : CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) *
      (CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak Q N (2 * Q * (L + 1)) L) +
        CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.exceptional Q N (2 * Q * (L + 1)) L)) ≤
      2 * (N : ℝ) ^ (-5 / 3 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (-2 / 3 + δ) *
          ((N : ℝ) ^ (-1 + δ + δ) + (N : ℝ) ^ (-1 + δ + δ)) :=
        mul_le_mul hpair (add_le_add hweak hex')
          (add_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (sum_nonneg fun _ _ ↦ abs_nonneg _))
          (Real.rpow_nonneg hn.le _)
      _ = 2 * ((N : ℝ) ^ (-2 / 3 + δ) * (N : ℝ) ^ (-1 + δ + δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hproduct (by norm_num)
  have hgood := (hg N (by omega) L hband).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (show -7 / 3 + δ ≤ -5 / 3 + ε / 2 by dsimp [δ]; linarith only [hε]))
  have hfinite := NonDirectApartPartition.finite_bound Q N (2 * Q * (L + 1)) L hL
  calc
    _ ≤ 3 * (N : ℝ) ^ (-5 / 3 + ε / 2) := by linarith only [hfinite, hbad, hgood]
    _ ≤ (N : ℝ) ^ ((-5 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NonDirectApartCostUnderInputs
