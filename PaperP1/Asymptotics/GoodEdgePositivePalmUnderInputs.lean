module

public import PaperP1.Model.GoodEdgePositivePalm
public import PaperP1.Asymptotics.FiniteCompressedInteriorMass
public import PaperP1.Asymptotics.PrivateChannelMassPhase
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase

/-! # Positive Palm costs of actual compatible good edges from homogeneous seed bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgePositivePalmUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.GoodEdgePositivePalm
  PaperP1.FiniteCompressedInteriorMass

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b (ε / 2) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          GoodEdgePositivePalm.mass N H a b L G ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, hu⟩ := HomogeneousGoodPairExtensionsUnderInputs.uniform_mass
    a b ha hab hb2a hcop C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨⟨Ds, kg, ko, K⟩, ?_⟩
  intro hgeo
  obtain ⟨NM, _hNM, hm⟩ := hu (by
    simpa only [div_div, show (2 : ℝ) * 128 = 256 by norm_num] using hgeo.sourceCover)
    hgeo.ordinaryCover hgeo.sourceCurves hgeo.ordinaryCurves
  refine ⟨max 10 (max NG NM), by omega, ?_⟩
  intro N hN L H hband G hG
  exact (GoodEdgePositivePalm.finite_mass (by omega) (hg N (by omega) L hband).1 hG).trans
    (hm N (by omega) L H hband)

theorem uniform_normalized (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b (ε / 4) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          0 < beta N H a b L ∧
          GoodEdgePositivePalm.mass N H a b L G ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
          normalized N H a b L G ≤ (N : ℝ) ^ (-1 / 3 - 1 / (b : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := uniform_mass a b ha hab hb2a hcop C (ε / 2) (by positivity)
  obtain ⟨c, _k, hc, _hk, NP, hphase⟩ := PrivateChannelMassPhase.positive_phase C D a b ha hab hb2a hcop
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 / c)
    (-1 / 3 - 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NM, _hNM, hm⟩ := hp (by simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hgeo)
  refine ⟨max 10 (max NM (max NP (max NG (max NS NF)))), by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (hg N (by omega) L hband).1
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hbeta : (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ beta N H a b L := by
    rw [beta, CompatibleChannelEdges.joint_mass_eq (by omega) hab hlarge]
    have hh := (hphase N (by omega) L H hband hcut hH).1
    have hlower := mul_le_mul_of_nonneg_left hL hc.le
    have hlowerN := mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg hn.le (-1 + 1 / (b : ℝ)))
    nlinarith only [hh, hlowerN]
  have hbasepos : 0 < (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
  have hbpos : 0 < beta N H a b L := hbasepos.trans_le hbeta
  have hmass := hm N (by omega) L H hband G hG
  refine ⟨hbpos, hmass.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)), ?_⟩
  calc
    _ ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) / beta N H a b L :=
      div_le_div_of_nonneg_right hmass hbpos.le
    _ ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) / ((c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hn.le _) hbasepos hbeta
    _ = (2 / c) * (N : ℝ) ^ (-1 / 3 - 1 / (b : ℝ) + ε / 2) := by
      rw [show -1 / 3 - 1 / (b : ℝ) + ε / 2 = (-4 / 3 + ε / 2) - (-1 + 1 / (b : ℝ)) by ring,
        Real.rpow_sub hn]
      field_simp
    _ ≤ _ := by
      simpa only [show (-1 / 3 - 1 / (b : ℝ) + ε / 2) + ε / 2 = -1 / 3 - 1 / (b : ℝ) + ε by ring] using hf N (by omega)

theorem companion_T3_1 (D : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p23 p34 : Parameters, Hypotheses p23 3 (ε / 4) → Hypotheses p34 4 (ε / 4) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
          0 < beta N H 2 3 L ∧ 0 < beta N H 3 4 L ∧
          normalized N H 2 3 L G ≤ (N : ℝ) ^ (-2 / 3 + ε) ∧
          normalized N H 3 4 L G ≤ (N : ℝ) ^ (-1 / 2 + ε) ∧
          GoodEdgePositivePalm.mass N H 2 3 L G ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
          GoodEdgePositivePalm.mass N H 3 4 L G ≤ (N : ℝ) ^ (-5 / 4 + ε) := by
  obtain ⟨p23, h23⟩ := uniform_normalized 2 3 D (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨p34, h34⟩ := uniform_normalized 3 4 D (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨p23, p34, ?_⟩
  intro hg23 hg34
  obtain ⟨N23, _hN23, h23⟩ := h23 hg23
  obtain ⟨N34, _hN34, h34⟩ := h34 hg34
  refine ⟨max 10 (max N23 N34), by omega, ?_⟩
  intro N hN L H hband hcut hH G hG
  obtain ⟨hb23, hm23, hn23⟩ := h23 N (by omega) L H hband (by omega) hH G hG
  obtain ⟨hb34, hm34, hn34⟩ := h34 N (by omega) L H hband (by omega) hH G hG
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  norm_num only [Nat.cast_ofNat] at hn23 hn34
  refine ⟨hb23, hb34, ?_, ?_, hm23, ?_⟩
  · convert hn23 using 1
    congr 1
    ring
  · exact hn34.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · exact hm34.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))

end PaperP1.GoodEdgePositivePalmUnderInputs
