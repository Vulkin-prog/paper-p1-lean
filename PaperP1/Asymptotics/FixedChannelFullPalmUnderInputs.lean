module

public import PaperP1.Model.GoodEdgeFullPalm
public import PaperP1.Asymptotics.FixedChannelAlignedTargetRate
public import PaperP1.Asymptotics.FixedChannelNonalignedMassUnderInputs
public import PaperP1.Asymptotics.NominalMarginalBias
public import PaperP1.Asymptotics.ConditionalNegativeDeviation
public import PaperP1.Asymptotics.GoodEdgePositivePalmUnderInputs
public import PaperP1.Model.PrivateChannelOrientationWeights

/-! # The complete original fixed-channel Palm mean of companion T2.7

All original target sites are retained. The only external arguments are
the existing finite geometric properties; the target estimate is proved
from the coarse asymmetric profile, the actual gamma rank and branching.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelFullPalmUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.GoodEdgePositivePalm
  PaperP1.FiniteCompressedInteriorMass PaperP1.SourceConditionalDeviations
  PaperP1.FixedChannelGamma

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def eta (a b : ℕ) : ℝ := min (17 / 24 : ℝ) (1 - gammaReal a b)

def mean (N H a b L : ℕ) : ℝ :=
  (∑ e ∈ CompatibleChannelEdges.edges N H a b L,
    infiniteJointMoment L e * freshMean N L e) / beta N H a b L

theorem eta_bounds {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) : (1 / 3 : ℝ) ≤ eta a b ∧ eta a b ≤ 2 / 3 := by
  have hu := gammaReal_le_two_thirds hcop (by omega : 3 ≤ b)
  have hl := FixedChannelGammaLower.gammaReal_ge_one_third ha hab hb2a hcop
  rw [eta, FixedChannelGammaLower.palm_exponent ha hab hb2a hcop]
  constructor <;> linarith only [hu, hl]

theorem ordered_mean {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    (∑ xy ∈ PrivateChannelSources.channelSources N H a b L,
      infiniteJointMoment L {xy.1, xy.2} * freshMean N L {xy.1, xy.2}) /
        PrivateChannelSources.channelMass N H a b L = mean N H a b L :=
  PrivateChannelOrientationWeights.normalized_weighted_sum hN hab hlarge _

theorem ordered_positive {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    (∑ xy ∈ PrivateChannelSources.channelSources N H a b L,
      infiniteJointMoment L {xy.1, xy.2} * positiveDeviation N L {xy.1, xy.2}) /
        PrivateChannelSources.channelMass N H a b L = normalized N H a b L (dyadicBlock N) := by
  rw [PrivateChannelOrientationWeights.normalized_weighted_sum hN hab hlarge]
  unfold normalized beta
  rw [iterated_mass]
  rfl

theorem uniform_normalized (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b (ε / 2) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        0 < beta N H a b L ∧
          normalized N H a b L (dyadicBlock N) ≤ (N : ℝ) ^ (-eta a b + ε) := by
  have hγ0 := FixedChannelGammaLower.gammaReal_ge_one_third ha hab hb2a hcop
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, hn⟩ := FixedChannelNonalignedMassUnderInputs.uniform_bound
    a b ha hab hcop C (ε / 4) (by positivity)
  obtain ⟨NA, _hNA, haM⟩ := FixedChannelAlignedTargetRate.uniform_bound a b ha hab hb2a hcop C (ε / 4) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := NominalMarginalBias.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨c, _k, hc, _hk, NP, hphase⟩ := PrivateChannelMassPhase.positive_phase C D a b ha hab hb2a hcop
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 + 4 / c)
    (-1 + gammaReal a b + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨⟨Ds, kg, ko, K⟩, ?_⟩
  intro hgeo
  obtain ⟨NN, _hNN, hn⟩ := hn (by
    simpa only [div_div, show (4 : ℝ) * 64 = 256 by norm_num,
      show (2 : ℝ) * 128 = 256 by norm_num] using hgeo.sourceCover)
    hgeo.ordinaryCover hgeo.sourceCurves hgeo.ordinaryCurves
  refine ⟨max 10 (max NN (max NA (max NB (max NP (max NG (max NS NF)))))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := (hg N (by omega) L hband).1
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hbeta : (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ beta N H a b L := by
    rw [beta, CompatibleChannelEdges.joint_mass_eq (by omega) hab hlarge]
    have hh := (hphase N (by omega) L H hband hcut hH).1
    have hlower := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 hc.le)
      (Real.rpow_nonneg hnpos.le (-1 + 1 / (b : ℝ)))
    nlinarith only [hh, hlower]
  have hbbase : 0 < (c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
  have hbpos : 0 < beta N H a b L := hbbase.trans_le hbeta
  have hnon : CompressedNonalignedInteractionMass.channelMass N a b L ≤
      (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) :=
    (hn N (by omega) L hband).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hγ0]))
  have halign := haM N (by omega) L hband
  have hparts : GoodEdgePositivePalm.mass N H a b L (dyadicBlock N) ≤
      beta N H a b L * (N : ℝ) ^ (-1 + ε / 4) +
        2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) := by
    have hfinite := GoodEdgeFullPalm.finite_mass (N := N) (H := H) (a := a) (b := b) hL Subset.rfl
    have hBias := mul_le_mul_of_nonneg_left (hb N (by omega) L hband (dyadicBlock N) Subset.rfl) hbpos.le
    linarith only [hfinite, hBias, hnon, halign]
  have hratio : (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) / beta N H a b L ≤
      (2 / c) * (N : ℝ) ^ (-1 + gammaReal a b + ε / 4) := by
    calc
      _ ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) /
          ((c / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) hbbase hbeta
      _ = _ := by
        rw [show -1 + gammaReal a b + ε / 4 =
          (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) - (-1 + 1 / (b : ℝ)) by ring,
          Real.rpow_sub hnpos]
        field_simp
  refine ⟨hbpos, ?_⟩
  have hquot : normalized N H a b L (dyadicBlock N) ≤
      (N : ℝ) ^ (-1 + ε / 4) + 2 * ((N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 4) / beta N H a b L) := by
    unfold normalized
    exact (div_le_div_of_nonneg_right hparts hbpos.le).trans_eq (by field_simp)
  have hbias : (N : ℝ) ^ (-1 + ε / 4) ≤ (N : ℝ) ^ (-1 + gammaReal a b + ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hγ0])
  have hbound : normalized N H a b L (dyadicBlock N) ≤
      (1 + 4 / c) * (N : ℝ) ^ (-1 + gammaReal a b + ε / 4) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 + gammaReal a b + ε / 4) +
          2 * ((2 / c) * (N : ℝ) ^ (-1 + gammaReal a b + ε / 4)) := by
        linarith only [hquot, hratio, hbias]
      _ = _ := by ring
  apply hbound.trans
  have heq : -eta a b + ε = -1 + gammaReal a b + ε := by
    rw [eta, FixedChannelGammaLower.palm_exponent ha hab hb2a hcop]
    ring
  rw [heq]
  simpa only [show (-1 + gammaReal a b + ε / 4) + 3 * ε / 4 = -1 + gammaReal a b + ε by ring] using hf N (by omega)

theorem finite_mean_upper {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hbpos : 0 < beta N H a b L) :
    mean N H a b L ≤ FiniteChannelHierarchy.nominalMean N L + normalized N H a b L (dyadicBlock N) := by
  have hsource : ∀ e ∈ CompatibleChannelEdges.edges N H a b L,
      freshMean N L e ≤ FiniteChannelHierarchy.nominalMean N L + positiveDeviation N L e := by
    intro e he
    have hsub := (PrivateChannelActivity.pair_data hN hab hlarge (mem_filter.mp he).1).1
    have hh := mean_decomposition (L := L) hsub
    have hn := negative_nonneg N L e
    have hs : 0 ≤ (e.card : ℝ) * (2 ^ L : ℝ)⁻¹ := by positivity
    linarith only [hh, hn, hs]
  have hpos : GoodEdgePositivePalm.mass N H a b L (dyadicBlock N) =
      ∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e * positiveDeviation N L e := by
    rw [iterated_mass]
    rfl
  have hsum : (∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e * freshMean N L e) ≤
      beta N H a b L * FiniteChannelHierarchy.nominalMean N L + GoodEdgePositivePalm.mass N H a b L (dyadicBlock N) := by
    calc
      _ ≤ ∑ e ∈ CompatibleChannelEdges.edges N H a b L,
          infiniteJointMoment L e * (FiniteChannelHierarchy.nominalMean N L + positiveDeviation N L e) :=
        sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_left (hsource e he) (infiniteJointMoment_nonneg L e))
      _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul, ← hpos]; rfl
  exact (div_le_div_of_nonneg_right hsum hbpos.le).trans_eq (by
    unfold normalized
    field_simp)

theorem mean_eq_conditional_integral {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    mean N H a b L = (∑ e ∈ CompatibleChannelEdges.edges N H a b L, infiniteJointMoment L e *
      ((∫ ω, if ω ∈ JointBranchingEvents.jointEvent e L then
        (infiniteStartCount (dyadicBlock N) L ω : ℝ) - 2 else 0
        ∂Model.InfiniteRademacher.infiniteRademacherMeasure) /
          Model.InfiniteRademacher.infiniteRademacherMeasure.real (JointBranchingEvents.jointEvent e L))) /
            beta N H a b L := by
  unfold mean
  congr 1
  apply sum_congr rfl
  intro e he
  obtain ⟨hsub, hcard⟩ := PrivateChannelActivity.pair_data hN hab hlarge (mem_filter.mp he).1
  rw [SourceConditionalCountMean.freshMean_eq_full_minus_source_integral N L e hL hsub, hcard]
  norm_num only [Nat.cast_ofNat]

theorem companion_T2_7 (a b D : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b (ε / 2) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        0 < beta N H a b L ∧
        normalized N H a b L (dyadicBlock N) ≤ (N : ℝ) ^ (-eta a b + ε) ∧
        |mean N H a b L - FiniteChannelHierarchy.nominalMean N L| ≤
          (N : ℝ) ^ (-min (eta a b) (1 / 2) + ε) := by
  obtain ⟨p, hp⟩ := uniform_normalized a b D ha hab hb2a hcop C ε hε
  obtain ⟨NM, _hNM, hm⟩ := ConditionalNegativeDeviation.uniform_mean_lower C 2 ε hε
  obtain ⟨NS, hs⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hp⟩ := hp hgeo
  refine ⟨max 10 (max NM (max NS NP)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  obtain ⟨hbpos, hpos⟩ := hp N (by omega) L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hs N (by omega) L hband
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hlower : FiniteChannelHierarchy.nominalMean N L - (N : ℝ) ^ (-1 / 2 + ε) ≤ mean N H a b L := by
    apply (le_div_iff₀ hbpos).mpr
    rw [beta, mul_sum]
    apply sum_le_sum
    intro e he
    obtain ⟨hsub, hcard⟩ := PrivateChannelActivity.pair_data (by omega) hab hlarge (mem_filter.mp he).1
    have hh := hm N (by omega) L hband e hsub (by omega) (mem_filter.mp he).2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (infiniteJointMoment_nonneg L e)
  have hupper := finite_mean_upper (H := H) (by omega : 2 ≤ N) hab hlarge hbpos
  have hposBound : (N : ℝ) ^ (-eta a b + ε) ≤ (N : ℝ) ^ (-min (eta a b) (1 / 2) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by have hh := min_le_left (eta a b) (1 / 2); linarith only [hh])
  have hnegBound : (N : ℝ) ^ (-1 / 2 + ε) ≤ (N : ℝ) ^ (-min (eta a b) (1 / 2) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by have hh := min_le_right (eta a b) (1 / 2); linarith only [hh])
  refine ⟨hbpos, hpos, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith only [hlower, hupper, hpos, hposBound, hnegBound]

end PaperP1.FixedChannelFullPalmUnderInputs
