module

public import PaperP1.Asymptotics.GoodEdgePositivePalm
public import PaperP1.Asymptotics.HomogeneousEffectiveGoodPairExtensions

/-! # Sharp positive Palm costs through the actual homogeneous crossing population

The finite comparison uses only the positive-excess support, retaining its
separation and nonzero crossing. The existing positive homogeneous 41/30
bound then improves every fixed interior channel by 1/30. The old companion
T3.1 remains a weaker consequence; no signed cancellation is used here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpGoodEdgePositivePalm

open Finset PaperP1.Model PaperP1.GoodEdgePositivePalm

theorem finite_mass {N H a b L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ RegularStarts.regularStarts N L) :
    GoodEdgePositivePalm.mass N H a b L G ≤
      HomogeneousEffectiveGoodPairExtensions.mass N H a b L := by
  classical
  refine (GoodEdgePositivePalm.finite_mass hN hL hG).trans ?_
  change (∑ p ∈ HomogeneousGoodPairExtensionsUnderInputs.points N H a b L,
      HomogeneousRunMass.probability L (SingletonExtensionWeights.join p)) ≤
    ∑ p ∈ HomogeneousEffectiveGoodPairExtensions.points N H a b L,
      HomogeneousRunMass.probability L (SingletonExtensionWeights.join p)
  apply sum_le_sum_of_subset_of_nonneg _
    (fun p _ _ ↦ (HomogeneousRunMass.probability_pos L (SingletonExtensionWeights.join p)).le)
  intro p hp
  obtain ⟨hbox, hfresh, hsep, hcross⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  exact mem_filter.mpr ⟨mem_product.mpr ⟨he, RegularStarts.regularStarts_subset N L hz⟩,
    hfresh, hsep, hcross⟩

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          GoodEdgePositivePalm.mass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousEffectiveGoodPairExtensions.uniform_mass
    a b ha hab hb2a hcop C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NG NM), by omega, ?_⟩
  intro N hN L H hband G hG
  exact (finite_mass (by omega) (hg N (by omega) L hband).1 hG).trans
    (hm N (by omega) L H hband)

theorem uniform_normalized (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          0 < GoodEdgePositivePalm.beta N H a b L ∧
          GoodEdgePositivePalm.mass N H a b L G ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
          GoodEdgePositivePalm.normalized N H a b L G ≤
            (N : ℝ) ^ (-11 / 30 - 1 / (b : ℝ) + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass a b ha hab hb2a hcop C (ε / 2) (by positivity)
  obtain ⟨c, _k, hc, _hk, NP, hphase⟩ := PrivateChannelMassPhase.positive_phase C D a b ha hab hb2a hcop
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 / c)
    (-11 / 30 - 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NM (max NP (max NG (max NS NF)))), by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (hg N (by omega) L hband).1
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hbeta : (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ GoodEdgePositivePalm.beta N H a b L := by
    rw [GoodEdgePositivePalm.beta, CompatibleChannelEdges.joint_mass_eq (by omega) hab hlarge]
    have hh := (hphase N (by omega) L H hband hcut hH).1
    have hlower := mul_le_mul_of_nonneg_left hL hc.le
    have hlowerN := mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg hn.le (-1 + 1 / (b : ℝ)))
    nlinarith only [hh, hlowerN]
  have hbasepos : 0 < (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
  have hbpos : 0 < GoodEdgePositivePalm.beta N H a b L := hbasepos.trans_le hbeta
  have hmass := hm N (by omega) L H hband G hG
  refine ⟨hbpos, hmass.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)), ?_⟩
  calc
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) / GoodEdgePositivePalm.beta N H a b L :=
      div_le_div_of_nonneg_right hmass hbpos.le
    _ ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) / ((c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) hbasepos hbeta
    _ = (2 / c) * (N : ℝ) ^ (-11 / 30 - 1 / (b : ℝ) + ε / 2) := by
      rw [show -11 / 30 - 1 / (b : ℝ) + ε / 2 = (-41 / 30 + ε / 2) - (-1 + 1 / (b : ℝ)) by ring,
        Real.rpow_sub hn]
      field_simp
    _ ≤ _ := by
      simpa only [show (-11 / 30 - 1 / (b : ℝ) + ε / 2) + ε / 2 = -11 / 30 - 1 / (b : ℝ) + ε by ring]
        using hf N (by omega)

theorem companion_T3_1_sharp (D : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          0 < GoodEdgePositivePalm.beta N H 2 3 L ∧
          0 < GoodEdgePositivePalm.beta N H 3 4 L ∧
          GoodEdgePositivePalm.normalized N H 2 3 L G ≤ (N : ℝ) ^ (-7 / 10 + ε) ∧
          GoodEdgePositivePalm.normalized N H 3 4 L G ≤ (N : ℝ) ^ (-37 / 60 + ε) ∧
          GoodEdgePositivePalm.mass N H 2 3 L G ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
          GoodEdgePositivePalm.mass N H 3 4 L G ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨N23, _hN23, h23⟩ := uniform_normalized 2 3 D (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨N34, _hN34, h34⟩ := uniform_normalized 3 4 D (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨max 10 (max N23 N34), by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  obtain ⟨hb23, hm23, hn23⟩ := h23 N (by omega) L H hband (by omega) hH G hG
  obtain ⟨hb34, hm34, hn34⟩ := h34 N (by omega) L H hband (by omega) hH G hG
  norm_num only [Nat.cast_ofNat] at hn23 hn34
  refine ⟨hb23, hb34, ?_, ?_, hm23, hm34⟩
  · convert hn23 using 1; norm_num
  · convert hn34 using 1; norm_num

end PaperP1.SharpGoodEdgePositivePalm
