module

public import PaperP1.Model.DependentSeedCover
public import PaperP1.Asymptotics.ConnectedSeedCatalogUnderInputs
public import PaperP1.Asymptotics.DependentPairJointMassUnderInputs
public import PaperP1.Asymptotics.VariableSeedMassPropagation

/-! # The full actual dependent joint mass has rate2/3 at every prescribed bounded order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedDependentJointMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pc : Parameters R, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 4) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 2 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        DependentFamilySeeds.dependentMass G L r ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  classical
  obtain ⟨pc, hc⟩ := ConnectedSeedCatalogUnderInputs.uniform_mass R C (ε / 4) (by positivity)
  obtain ⟨pp, hp⟩ := DependentPairJointMassUnderInputs.uniform_bound C (ε / 4) (by positivity)
  have hprop (i : Fin (R + 1)) := VariableSeedMassPropagation.uniform_mass i.val C (ε / 4) (by positivity)
  choose NR hr using hprop
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-2 / 3 + ε / 4) (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (R.factorial : ℝ)
    (-2 / 3 + 3 * ε / 4) (ε / 4) (by positivity)
  refine ⟨pc, pp, ?_⟩
  intro hgeoC hgeoP
  have hscale : (ε / 4) / 1024 = ε / 4096 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc hgeoC
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [hscale] using hgeoP)
  refine ⟨10 + NC + NP + NG + NF + NA + univ.sup NR, by omega, ?_⟩
  intro N hN L hband r htwo hcap G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcatalog := (hc N (by omega) L hband G hG).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-1 : ℝ) + ε / 4 ≤ -2 / 3 + ε / 4))
  have hpair := hp N (by omega) L hband G hG
  have hfinite := GraphStarWeights.sum_union_le_nonneg (DependentFamilySeeds.dependentFamilies G L 2)
    (ConnectedSeedCatalog.families G L R) (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  change (∑ D ∈ DependentSeedCover.families G L R, infiniteJointMoment L D) ≤ _ at hfinite
  have hfactor : 2 * (N : ℝ) ^ (-2 / 3 + ε / 4) ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hseed : (∑ D ∈ DependentSeedCover.families G L R, infiniteJointMoment L D) ≤
      (N : ℝ) ^ (-2 / 3 + ε / 2) := by linarith only [hcatalog, hpair, hfinite, hfactor]
  let S := (DependentSeedCover.families G L R).filter fun D ↦ D.card ≤ r
  let i : Fin (R + 1) := ⟨r, by omega⟩
  have hiN : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
  have hsource (D : Finset ℕ) (hD : D ∈ S) : D ⊆ dyadicBlock N ∧ 1 ≤ D.card ∧ D.card ≤ r := by
    obtain ⟨hDS, hcard⟩ := mem_filter.mp hD
    have hd := DependentSeedCover.family_data G L R D hDS
    exact ⟨hd.1.trans hG, by omega, hcard⟩
  have htarget (I : Finset ℕ) (hI : I ∈ DependentFamilySeeds.dependentFamilies G L r) :
      I ⊆ dyadicBlock N ∧ I.card = r ∧ ∃ D ∈ S, D ⊆ I := by
    obtain ⟨hIG, hdep⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
    obtain ⟨D, hD, hDI⟩ := DependentSeedCover.cover G L R I hsub (by omega) hdep
    exact ⟨hsub.trans hG, hcard, D, mem_filter.mpr ⟨hD, by have h := card_le_card hDI; omega⟩, hDI⟩
  have hS : (∑ D ∈ S, infiniteJointMoment L D) ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun D _ _ ↦ infiniteJointMoment_nonneg L D)).trans hseed
  have hraw := hr i N (by omega) L hL hband S hsource (DependentFamilySeeds.dependentFamilies G L r) htarget
  have hfact : (r.factorial : ℝ) ≤ R.factorial := by exact_mod_cast Nat.factorial_le hcap
  calc
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-2 / 3 + ε / 2) := hraw.trans
      (mul_le_mul_of_nonneg_left hS (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)))
    _ ≤ (R.factorial : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-2 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfact (Real.rpow_nonneg hn.le _))
        (Real.rpow_nonneg hn.le _)
    _ = (R.factorial : ℝ) * (N : ℝ) ^ (-2 / 3 + 3 * ε / 4) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ _ := by
      convert ha N (by omega) using 1
      congr 1
      ring

end PaperP1.FixedDependentJointMassUnderInputs
