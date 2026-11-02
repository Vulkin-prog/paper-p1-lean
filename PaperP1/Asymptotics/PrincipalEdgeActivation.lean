module

public import PaperP1.Model.ActiveEdgeObservables
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase
public import PaperP1.Asymptotics.SubpowerFixedCountMoments

/-! # The actual probability of an active principal edge is N^(-2/3+o(1)), without BCN -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeActivation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges
  PaperP1.ActiveEdgeObservables

theorem uniform_probability (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (N : ℝ) ^ (-2 / 3 - ε) ≤ probability (edges N H L) L ∧
        probability (edges N H L) L ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨k, hk⟩ := exists_nat_ge (2 / δ)
  have hdk : 2 ≤ δ * k := by
    have h := (div_le_iff₀ hδ).mp hk
    linarith only [h]
  let m := 2 + k
  have hm : 2 ≤ m := by dsimp [m]; omega
  obtain ⟨c, K, hc, hK, NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NM, _hNM, hmoment⟩ := SubpowerFixedCountMoments.uniform_ordinary m C (1 / 2) (by norm_num)
  obtain ⟨NT, ht⟩ := HalfCountSchedule.factor_absorption (2 / c) (-3 / 2) (5 / 6) (by norm_num)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 / c) (-2 / 3 - ε) (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NU, hu⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (K * CriticalBandScale.upperScale) 1 ε hε
  refine ⟨max 2 (max NP (max NG (max NM (max NT (max NF (max NS NU)))))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hband
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hF := PrincipalChannelEdges.subset_pairs (H := H) (by omega) hlarge
  have hcutF : ∀ e ∈ edges N H L, ∀ x ∈ e, x + L ≤ dyadicCutoff N L := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff (subset_refl (dyadicBlock N)) x ((mem_powersetCard.mp (hF he)).1 hx)
  let R := (N : ℝ) ^ δ
  have hR : 0 < R := Real.rpow_pos_of_pos hn _
  have hpow (j : ℕ) : R ^ j = (N : ℝ) ^ (δ * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have htail : CountObservables.countMoment (dyadicBlock N) L m / R ^ (m - 2) ≤
      (c / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / R ^ (m - 2) := div_le_div_of_nonneg_right
        (hmoment N (by omega) L hband (dyadicBlock N) (subset_refl _)) (pow_nonneg hR.le _)
      _ = (N : ℝ) ^ (1 / 2 - δ * k) := by
        rw [show m - 2 = k by dsimp [m]; omega, hpow, ← Real.rpow_sub hn]
      _ ≤ (N : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hdk])
      _ ≤ (c / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
        have h := mul_le_mul_of_nonneg_left (ht N (by omega)) (by positivity : 0 ≤ c / 2)
        have hid : (c / 2) * (2 / c) = 1 := by field_simp
        norm_num only [show (-3 / 2 : ℝ) + 5 / 6 = -2 / 3 by ring] at h
        simpa only [← mul_assoc, hid, one_mul, neg_div] using h
  have htrunc := ActiveEdgeObservables.truncation (L := L) (subset_refl (dyadicBlock N))
    (edges N H L) hF R hR m hm
  change beta N H L ≤ _ at htrunc
  have hphase := hp N (by omega) L H hband hcut hH
  have hlower : (c / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ R ^ 2 * probability (edges N H L) L := by
    have hbase : c * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ c * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_left hL1 (by positivity : 0 ≤ c * (N : ℝ) ^ (-2 / 3 : ℝ))]
    have hmean : c * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ beta N H L := hbase.trans hphase.1
    linarith only [hmean, htail, htrunc]
  have hlowerP : (c / 2) * (N : ℝ) ^ (-2 / 3 - ε / 2) ≤ probability (edges N H L) L := by
    apply (mul_le_mul_iff_of_pos_right (pow_pos hR 2)).mp
    calc
      _ = (c / 2) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
        rw [hpow]
        dsimp [δ]
        rw [mul_assoc, ← Real.rpow_add hn]
        congr 1
        congr 1
        ring
      _ ≤ R ^ 2 * probability (edges N H L) L := hlower
      _ = probability (edges N H L) L * R ^ 2 := mul_comm _ _
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left (hf N (by omega)) (by positivity : 0 ≤ c / 2)
    have hid : (c / 2) * (2 / c) = 1 := by field_simp
    have hlow : (N : ℝ) ^ (-2 / 3 - ε) ≤ (c / 2) * (N : ℝ) ^ (-2 / 3 - ε / 2) := by
      convert h using 1
      · rw [← mul_assoc, hid, one_mul]
      · congr 2
        ring
    exact hlow.trans hlowerP
  · have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    have hpoly : K * L ≤ (N : ℝ) ^ ε := by
      calc
        _ ≤ K * (CriticalBandScale.upperScale * Real.log N) :=
          mul_le_mul_of_nonneg_left (hLB.trans (hs N (by omega) L hband).2) hK.le
        _ = (K * CriticalBandScale.upperScale) * Real.log N := by ring
        _ ≤ _ := by simpa only [Real.rpow_one] using hu N (by omega)
    calc
      _ ≤ beta N H L := probability_le_mass (edges N H L) hcutF
      _ ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := hphase.2
      _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.PrincipalEdgeActivation
