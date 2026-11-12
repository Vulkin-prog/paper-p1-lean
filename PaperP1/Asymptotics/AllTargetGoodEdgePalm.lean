module

public import PaperP1.Model.AllTargetGoodEdgePalm
public import PaperP1.Asymptotics.GoodEdgePositivePalm
public import PaperP1.Model.RegularSetAsymptotic

/-! # V2 companion T10.5: exact and nominal Palm costs on all dyadic targets

The exact positive excess is controlled by the genuine homogeneous effective
crossing population. Nominal recentering uses the independently proved total
marginal discrepancy. A positive compatible source phase is established before
normalization. Every fixed parameter precedes N,L,H and the target set.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.AllTargetGoodEdgePalm

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Probability PaperP1.RegularAffineBounds PaperP1.RegularStarts

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem uniform_exact_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        exactMass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass a b ha hab hb2a hcop C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨10 + NM + NG, by omega, ?_⟩
  intro N hN L H hband G hG
  exact (finite_exact_mass (hg N (by omega) L hband).1 hG).trans (hm N (by omega) L H hband)

theorem uniform_marginal_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → marginalError N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NM, hm⟩ := RegularSetAsymptotic.affine_marginal_sum_critical C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NM + NG + NA, by omega, ?_⟩
  intro N hN L hband
  have hL := (hg N (by omega) L hband).1
  have hraw : marginalError N L ≤ (2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ (ε / 2) := by
    simpa only [marginalError, affineWindowMass, infiniteMarginal_eq_affine_atom hL] using
      hm N (by omega) L hL hband (dyadicBlock N) (subset_refl _) (fun _ ↦ startRhs L)
  calc
    _ ≤ (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε / 2) :=
      hraw.trans (RegularSetAsymptotic.nominal_times_rpow_bound (by omega) hband)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_source_phase (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      c * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ GoodEdgePositivePalm.beta N H a b L ∧
      GoodEdgePositivePalm.beta N H a b L ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ) + η) ∧
      0 < GoodEdgePositivePalm.beta N H a b L := by
  obtain ⟨c, k, hc, hk, NP, hphase⟩ := PrivateChannelMassPhase.positive_phase C D a b ha hab hb2a hcop
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NB, hb⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NU, hu⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le (k / 2) 1 η hη
  refine ⟨c / 2, by positivity, 10 + NP + NG + NS + NB + NU, by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (hg N (by omega) L hband).1
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hbetaeq : GoodEdgePositivePalm.beta N H a b L =
      PrivateChannelSources.channelMass N H a b L / 2 :=
    CompatibleChannelEdges.joint_mass_eq (by omega) hab hlarge
  have hphaseN := hphase N (by omega) L H hband hcut hH
  have hlower : (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ GoodEdgePositivePalm.beta N H a b L := by
    rw [hbetaeq]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hc.le)
      (Real.rpow_nonneg hn.le (-1 + 1 / (b : ℝ)))
    nlinarith only [hh, hphaseN.1]
  have hpoly : (k / 2) * (L : ℝ) ≤ (N : ℝ) ^ η := by
    have hh := hu N (by omega) L (hb N (by omega) L hband).2
    simp only [pow_one, abs_of_nonneg (by positivity : 0 ≤ (k / 2) * (L + 1 : ℝ))] at hh
    have hstep : (k / 2) * (L : ℝ) ≤ (k / 2) * (L + 1 : ℝ) := by nlinarith only [hk]
    exact hstep.trans hh
  have hbpos : 0 < GoodEdgePositivePalm.beta N H a b L := by
    have hp : 0 < (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
    exact hp.trans_le hlower
  refine ⟨hlower, ?_, hbpos⟩
  calc
    _ ≤ ((k / 2) * (L : ℝ)) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
      rw [hbetaeq]
      nlinarith only [hphaseN.2]
    _ ≤ (N : ℝ) ^ η * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_combined_mass (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        0 < GoodEdgePositivePalm.beta N H a b L ∧
        combinedMass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := uniform_exact_mass a b ha hab hb2a hcop C (ε / 4) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := uniform_marginal_error C (ε / 4) (by positivity)
  obtain ⟨c, _hc, NP, _hNP, hp⟩ := uniform_source_phase a b D ha hab hb2a hcop C (ε / 4) (by positivity)
  obtain ⟨NA, haF⟩ := HalfCountSchedule.factor_absorption 3 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NE + NM + NP + NA, by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨_hlower, hbupper, hbpos⟩ := hp N (by omega) L H hband hcut hH
  have herror : GoodEdgePositivePalm.beta N H a b L * marginalError N L ≤
      (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε / 4) * (N : ℝ) ^ (-1 + ε / 4) :=
        mul_le_mul hbupper (hm N (by omega) L hband)
          (sum_nonneg fun z _ ↦ abs_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have hrecip : 1 / (b : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
          (by exact_mod_cast (show 3 ≤ b by omega))
        linarith only [hrecip]
  have hexact : exactMass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := (he N (by omega) L H hband G hG).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hnom := finite_nominal_mass (H := H) (a := a) (b := b) (L := L) hG
  refine ⟨hbpos, ?_⟩
  calc
    _ ≤ 3 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
      change exactMass N H a b L G + GoodEdgePositivePalm.mass N H a b L G ≤ _
      linarith only [hexact, hnom, herror]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := haF N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T10_5 (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      6 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        0 < GoodEdgePositivePalm.beta N H a b L ∧
        combinedMass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
        normalized N H a b L G ≤ (N : ℝ) ^ (-11 / 30 - 1 / (b : ℝ) + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_combined_mass a b D ha hab hb2a hcop C (ε / 2) (by positivity)
  obtain ⟨c, hc, NP, _hNP, hp⟩ := uniform_source_phase a b D ha hab hb2a hcop C 1 (by norm_num)
  obtain ⟨NA, haF⟩ := HalfCountSchedule.factor_absorption (1 / c)
    (-11 / 30 - 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NM + NP + NA, by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  have hcut' : 2 * b * (L + 1) ≤ H :=
    (Nat.mul_le_mul_right (L + 1) (by omega : 2 * b ≤ 6 * b)).trans hcut
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hbpos, hmass⟩ := hm N (by omega) L H hband hcut' hH G hG
  have hbeta := (hp N (by omega) L H hband hcut' hH).1
  have hbase : 0 < c * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
  refine ⟨hbpos, hmass.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)), ?_⟩
  calc
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) / GoodEdgePositivePalm.beta N H a b L :=
      div_le_div_of_nonneg_right hmass hbpos.le
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) / (c * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) hbase hbeta
    _ = (1 / c) * (N : ℝ) ^ (-11 / 30 - 1 / (b : ℝ) + ε / 2) := by
      rw [show -11 / 30 - 1 / (b : ℝ) + ε / 2 = (-41 / 30 + ε / 2) - (-1 + 1 / (b : ℝ)) by ring,
        Real.rpow_sub hn]
      field_simp
    _ ≤ (N : ℝ) ^ ((-11 / 30 - 1 / (b : ℝ) + ε / 2) + ε / 2) := haF N (by omega)
    _ = _ := by congr 1; ring

theorem principal_channels (D : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      24 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        0 < GoodEdgePositivePalm.beta N H 2 3 L ∧
        0 < GoodEdgePositivePalm.beta N H 3 4 L ∧
        GoodEdgePositivePalm.normalized N H 2 3 L G ≤ (N : ℝ) ^ (-7 / 10 + ε) ∧
        GoodEdgePositivePalm.normalized N H 3 4 L G ≤ (N : ℝ) ^ (-37 / 60 + ε) ∧
        combinedMass N H 2 3 L G ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
        combinedMass N H 3 4 L G ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨N23, _hN23, h23⟩ := companion_T10_5 2 3 D (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨N34, _hN34, h34⟩ := companion_T10_5 3 4 D (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨10 + N23 + N34, by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  obtain ⟨hb23, hm23, hn23⟩ := h23 N (by omega) L H hband (by omega) hH G hG
  obtain ⟨hb34, hm34, hn34⟩ := h34 N (by omega) L H hband (by omega) hH G hG
  have hp23 := (nominal_normalized_le N H 2 3 L G).trans hn23
  have hp34 := (nominal_normalized_le N H 3 4 L G).trans hn34
  norm_num only [Nat.cast_ofNat] at hp23 hp34
  refine ⟨hb23, hb34, ?_, ?_, hm23, hm34⟩
  · convert hp23 using 1; norm_num
  · convert hp34 using 1; norm_num

end PaperP1.AllTargetGoodEdgePalm
