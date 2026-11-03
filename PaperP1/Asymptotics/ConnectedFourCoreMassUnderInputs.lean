module

public import PaperP1.Asymptotics.LargePositiveCoreTail
public import PaperP1.Asymptotics.FixedConnectedJointWeightedUnderInputs
public import PaperP1.Asymptotics.FixedConnectedWeightedUnderInputs
public import PaperP1.Model.PrimitiveActualMass

/-! # Every actual connected four-core below two ranks has all-cardinality joint-plus-centered mass rate1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedFourCoreMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies PaperP1.RelationCoreWitnesses

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ pc pi pj : Parameters s, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 64) → Hypotheses pi (ε / 256) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 262144)) →
      Hypotheses pj (ε / 16) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧ Core 4 L I ∧ runRelativeNullity L I ≤ 2 * L) →
        (∑ I ∈ F, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
          (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := LargePositiveCoreTail.uniform_rank 4 2 u C (ε / 2)
    (by decide) (by norm_num) (by norm_num) (by norm_num) hu (by positivity)
  obtain ⟨pc, pi, pp, hc⟩ := FixedConnectedWeightedUnderInputs.uniform_bound s u C (ε / 2) hu.le (by positivity)
  obtain ⟨pj, hj⟩ := FixedConnectedJointWeightedUnderInputs.uniform_bound s u C (ε / 2) hu.le (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, pc, pi, pj, pp, ?_⟩
  intro hgeoC hgeoI hgeoP hgeoJ
  have hsC : (ε / 2) / 32 = ε / 64 := by ring
  have hsI : (ε / 2) / 128 = ε / 256 := by ring
  have hsP : (ε / 2) / 131072 = ε / 262144 := by ring
  have hsJ : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
  obtain ⟨NJ, _hNJ, hj⟩ := hj (by simpa only [hsJ] using hgeoJ)
  refine ⟨10 + NT + NG + NF + NC + NJ, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let P := fun I : Finset ℕ ↦ I.card < s
  let FS := F.filter P
  let FT := F.filter fun I ↦ ¬ P I
  have hsmallData : ∀ I ∈ FS, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ s ∧ Connected L I := by
    intro I hI
    obtain ⟨hIF, hsmall⟩ := mem_filter.mp hI
    obtain ⟨hIG, hthree, hconn, _hcore, _hrank⟩ := hF I hIF
    exact ⟨hIG, hthree, by dsimp only [P] at hsmall; omega, hconn⟩
  have hsmall : (∑ I ∈ FS, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
      2 * (N : ℝ) ^ (-1 + ε / 2) := by
    have hq := hj N (by omega) L hband G hG FS hsmallData
    have hc := hc N (by omega) L hband G hG FS hsmallData
    simp_rw [mul_add]
    rw [sum_add_distrib]
    linarith only [hq, hc]
  have htail : (∑ I ∈ FT, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
      2 * (N : ℝ) ^ (-1 + ε / 2) := by
    have hdata : ∀ I ∈ FT, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ Core 4 L I ∧
        (runRelativeNullity L I : ℝ) ≤ 2 * L := by
      intro I hI
      obtain ⟨hIF, hsmall⟩ := mem_filter.mp hI
      obtain ⟨hIG, _hthree, _hconn, hcore, hrank⟩ := hF I hIF
      exact ⟨hIG.trans hG, by dsimp only [P] at hsmall; omega, hcore, by exact_mod_cast hrank⟩
    have hrank := ht N (by omega) L hband FT hdata
    have hactual := PrimitiveActualMass.actual_le_rank FT L hL u hu.le (by
      intro I hI
      exact card_pos.mp (by have h := (hdata I hI).2.1; omega))
    have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
    exact hactual.trans ((mul_le_mul_of_nonneg_left hrank (by norm_num)).trans
      (mul_le_mul_of_nonneg_left hpower (by norm_num)))
  have hsplit := sum_filter_add_sum_filter_not F P
    (fun I ↦ u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|))
  change (∑ I ∈ FS, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
    (∑ I ∈ FT, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) = _ at hsplit
  have hfactor : 4 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hsmall, htail, hsplit, hfactor]

end PaperP1.ConnectedFourCoreMassUnderInputs
