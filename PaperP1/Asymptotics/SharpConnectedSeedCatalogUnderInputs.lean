module

public import PaperP1.Model.VariableConnectedSeedCatalog
public import PaperP1.Asymptotics.PrimitiveSharpMassUnderInputs
public import PaperP1.Asymptotics.ConnectedTriplePositiveUnderInputs
public import PaperP1.Asymptotics.SharpConnectedSeedParameters

/-! # Sharp positive connected seeds reduce to the literal third absolute activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpConnectedSeedCatalogUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.SharpConnectedSeedParameters

theorem uniform_mass (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ D ∈ VariableConnectedSeedCatalog.families G L R (ε / 8), infiniteJointMoment L D) ≤
        (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (connectedFamilies G L 3) +
        (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  have hprim (i : Fin (R + 1)) := PrimitiveSharpMassUnderInputs.article_15_5
    (max 4 i.val) (le_max_left _ _) C (ε / 8) (by positivity)
  choose pp hp using hprim
  have hdirect (i : Fin (R + 1)) := DirectCrossingSeedFamiliesUnderInputs.uniform_seeds
    (max 2 i.val) (le_max_left _ _) C (ε / 8) (by positivity)
  choose dp qp hd using hdirect
  obtain ⟨tp, ht⟩ := ConnectedTriplePositiveUnderInputs.uniform_reduction C (ε / 8) (by positivity)
  obtain ⟨lp, hl⟩ := LowTwoPairSeedsUnderInputs.uniform_seeds (ε / 8) C (ε / 8)
    (by positivity) (by positivity)
  obtain ⟨dd, dq, hdense⟩ := DensePairCrossingFamiliesUnderInputs.uniform_seeds C (ε / 8) (ε / 8)
    (by positivity) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let K : ℝ := 2 * ((R + 1 : ℕ) : ℝ) + 3
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K 0 (ε / 2) (by positivity)
  refine ⟨⟨pp, tp, lp, dd, dq, dp, qp⟩, ?_⟩
  intro hgeo
  have hpThreshold (i : Fin (R + 1)) := hp i (hgeo.primitive i)
  choose NP _hNP hp using hpThreshold
  have hsT : (ε / 8) / 1024 = ε / 8192 := by ring
  have hsL : (ε / 8) / 4096 = ε / 32768 := by ring
  have hsD : (ε / 8) / 2048 = ε / 16384 := by ring
  have hdThreshold (i : Fin (R + 1)) := hd i (hgeo.direct i)
    (by simpa only [hsD] using hgeo.directPair i)
  choose ND _hND hd using hdThreshold
  obtain ⟨NT, _hNT, ht⟩ := ht (by simpa only [hsT] using hgeo.triple)
  obtain ⟨NL, _hNL, hl⟩ := hl (by simpa only [hsL] using hgeo.lowPair)
  obtain ⟨NDense, _hNDense, hdense⟩ := hdense hgeo.dense (by simpa only [hsD] using hgeo.densePair)
  refine ⟨10 + NG + NF + NT + NL + NDense + univ.sup NP + univ.sup ND, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let A3 := CompatibleActivitySplit.absolute L (connectedFamilies G L 3)
  let P := (N : ℝ) ^ (-4 / 3 + ε / 4)
  have hA3 : 0 ≤ A3 := sum_nonneg fun D _ ↦ abs_nonneg _
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hpower : (N : ℝ) ^ (-5 / 3 + ε / 8) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  have htError : (N : ℝ) ^ (-3 / 2 + ε / 8) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
  have hT : TripleJointPopulations.connectedJointMass G L ≤ A3 + P :=
    (ht N (by omega) L hband G hG).trans (add_le_add le_rfl htError)
  have hP (h : ℕ) (hh : h ∈ Icc 3 R) :
      (∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) ≤ A3 + P := by
    by_cases hh3 : h = 3
    · subst h
      apply le_trans _ hT
      apply sum_le_sum_of_subset_of_nonneg
      · intro D hD
        obtain ⟨hDG, hprim⟩ := mem_filter.mp hD
        exact mem_filter.mpr ⟨hDG, PrimitiveConnectedGeometry.connected L D hprim⟩
      · intro D _ _
        exact infiniteJointMoment_nonneg L D
    · let i : Fin (R + 1) := ⟨h, by have h := (mem_Icc.mp hh).2; omega⟩
      have hiN : NP i ≤ univ.sup NP := le_sup (f := NP) (mem_univ i)
      have hmax : max 4 i.val = h := by
        change max 4 h = h
        exact max_eq_right (by have hthree := (mem_Icc.mp hh).1; omega)
      have hbound := (hp i N (by omega) L hband G hG (primitiveFamilies G L h) (by
        intro D hD
        obtain ⟨hDG, hprim⟩ := mem_filter.mp hD
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hDG
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, hcard.trans hmax.symm⟩, hprim⟩)).1
      have hm : (∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) ≤ P :=
        ((sum_le_sum (fun D _ ↦ PrimitiveWindowMass.joint_le_weight L hL D)).trans hbound).trans
          (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
      exact hm.trans (le_add_of_nonneg_left hA3)
  have hPSum : (∑ h ∈ Icc 3 R, ∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) ≤
      ((R + 1 : ℕ) : ℝ) * (A3 + P) := by
    calc
      _ ≤ ∑ _h ∈ Icc 3 R, (A3 + P) := sum_le_sum hP
      _ = ((Icc 3 R).card : ℝ) * (A3 + P) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Icc 3 R).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (add_nonneg hA3 hP0)
  have hDir (h : ℕ) (hh : h ∈ Icc 2 (R - 2)) :
      (∑ D ∈ DirectCrossingSeedFamilies.families G L h, infiniteJointMoment L D) ≤
        (N : ℝ) ^ (-4 / 3 + ε / 4) := by
    let i : Fin (R + 1) := ⟨h, by have h := (mem_Icc.mp hh).2; omega⟩
    have hiN : ND i ≤ univ.sup ND := le_sup (f := ND) (mem_univ i)
    have hmax : max 2 i.val = h := max_eq_right (mem_Icc.mp hh).1
    have hbound := hd i N (by omega) L hband G hG
    rw [hmax] at hbound
    exact hbound.trans hpower
  have hDirSum : (∑ h ∈ Icc 2 (R - 2), ∑ D ∈ DirectCrossingSeedFamilies.families G L h,
      infiniteJointMoment L D) ≤ ((R + 1 : ℕ) : ℝ) * P := by
    calc
      _ ≤ ∑ _h ∈ Icc 2 (R - 2), (N : ℝ) ^ (-4 / 3 + ε / 4) := sum_le_sum hDir
      _ = ((Icc 2 (R - 2)).card : ℝ) * (N : ℝ) ^ (-4 / 3 + ε / 4) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show (Icc 2 (R - 2)).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hLow := (hl N (by omega) L hband G hG).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε] : (-4 / 3 : ℝ) + ε / 8 + ε / 8 ≤ -4 / 3 + ε / 4))
  have hDense := (hdense N (by omega) L hband G hG).trans hpower
  have hfinite := VariableConnectedSeedCatalog.mass_bound G L R (ε / 8)
  have hraw : (∑ D ∈ VariableConnectedSeedCatalog.families G L R (ε / 8), infiniteJointMoment L D) ≤
      K * (A3 + P) := by
    dsimp [K]
    change (∑ D ∈ connectedFamilies G L 3, infiniteJointMoment L D) ≤ A3 + P at hT
    change (∑ D ∈ LowTwoPairSeeds.families G L (ε / 8), infiniteJointMoment L D) ≤ P at hLow
    change (∑ D ∈ DensePairCrossingSeeds.families G L (ε / 8), infiniteJointMoment L D) ≤ P at hDense
    nlinarith only [hfinite, hPSum, hDirSum, hT, hLow, hDense, hA3, hP0]
  have hconstant : K ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ K * (A3 + P) := hraw
    _ ≤ (N : ℝ) ^ (ε / 2) * (A3 + P) := mul_le_mul_of_nonneg_right hconstant (add_nonneg hA3 hP0)
    _ = (N : ℝ) ^ (ε / 2) * A3 + (N : ℝ) ^ (-4 / 3 + 3 * ε / 4) := by
      rw [mul_add]
      congr 1
      dsimp only [P]
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hA3)
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))

end PaperP1.SharpConnectedSeedCatalogUnderInputs
