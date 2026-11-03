module

public import PaperP1.Asymptotics.ConnectedOneRankOffsetMassUnderInputs
public import PaperP1.Asymptotics.ConnectedFourCoreMassUnderInputs
public import PaperP1.Asymptotics.AllPairDeficitUnderInputs
public import PaperP1.Model.CompressedPairMass

/-! # The whole compressed-pair mass has exponent one for every dependent source pair and every actual cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairPrimitiveCompression PaperP1.CompressedPairMass

structure Parameters where
  lowOrder : ℕ
  jointOrder : ℕ
  coreOrder : ℕ
  deficitOrders : ℕ
  lowConnected : CoarseConnectedParameters.Parameters lowOrder
  lowIncompatible : CoarseConnectedParameters.Parameters lowOrder
  lowJoint : CoarseConnectedParameters.Parameters jointOrder
  lowPair : FinitePairDeficitInputs.Parameters
  coreConnected : CoarseConnectedParameters.Parameters coreOrder
  coreIncompatible : CoarseConnectedParameters.Parameters coreOrder
  coreJoint : CoarseConnectedParameters.Parameters coreOrder
  corePair : FinitePairDeficitInputs.Parameters
  deficitInitial : FinitePairDeficitInputs.Parameters
  deficit : Fin deficitOrders → FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  lowConnected : CoarseConnectedParameters.Hypotheses p.lowConnected (ε / 512)
  lowIncompatible : CoarseConnectedParameters.Hypotheses p.lowIncompatible (ε / 2048)
  lowJoint : CoarseConnectedParameters.Hypotheses p.lowJoint (ε / 128)
  lowPair : FinitePairDeficitInputs.Hypotheses p.lowPair (GeneralGraphHostCount.sizeCap (ε / 2097152))
  coreConnected : CoarseConnectedParameters.Hypotheses p.coreConnected (ε / 128)
  coreIncompatible : CoarseConnectedParameters.Hypotheses p.coreIncompatible (ε / 512)
  coreJoint : CoarseConnectedParameters.Hypotheses p.coreJoint (ε / 32)
  corePair : FinitePairDeficitInputs.Hypotheses p.corePair (GeneralGraphHostCount.sizeCap (ε / 524288))
  deficitInitial : FinitePairDeficitInputs.Hypotheses p.deficitInitial (GeneralGraphHostCount.sizeCap (ε / 4096))
  deficit : ∀ i, FinitePairDeficitInputs.Hypotheses (p.deficit i) (GeneralGraphHostCount.sizeCap (ε / 131072))

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → mass (pairs G L) L u ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨sl, sj, _hsl, _hsj, plc, pli, plp, plj, hl⟩ :=
    ConnectedOneRankOffsetMassUnderInputs.uniform_bound (2 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨sc, _hsc, pcc, pci, pcj, pcp, hc⟩ :=
    ConnectedFourCoreMassUnderInputs.uniform_bound (2 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨_Q, sd, _hQ, _hsd, pd0, pd, hd⟩ := AllPairDeficitUnderInputs.article_15_9 u C (ε / 2) hu (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (4 + 2 * u ^ 2) (-1 + ε / 2) (ε / 2) (by positivity)
  let p : Parameters := ⟨sl, sj, sc, sd, plc, pli, plj, plp, pcc, pci, pcj, pcp, pd0, pd⟩
  refine ⟨p, ?_⟩
  intro hp
  have hsLC : (ε / 2) / 256 = ε / 512 := by ring
  have hsLI : (ε / 2) / 1024 = ε / 2048 := by ring
  have hsLJ : (ε / 2) / 64 = ε / 128 := by ring
  have hsLP : (ε / 2) / 1048576 = ε / 2097152 := by ring
  have hsCC : (ε / 2) / 64 = ε / 128 := by ring
  have hsCI : (ε / 2) / 256 = ε / 512 := by ring
  have hsCJ : (ε / 2) / 16 = ε / 32 := by ring
  have hsCP : (ε / 2) / 262144 = ε / 524288 := by ring
  have hsD0 : ((ε / 2) / 16) / 128 = ε / 4096 := by ring
  have hsD : ((ε / 2) / 16) / 4096 = ε / 131072 := by ring
  obtain ⟨NL, _hNL, hl⟩ := hl (by simpa only [hsLC] using hp.lowConnected)
    (by simpa only [hsLI] using hp.lowIncompatible) (by simpa only [hsLP] using hp.lowPair)
    (by simpa only [hsLJ] using hp.lowJoint)
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hsCC] using hp.coreConnected)
    (by simpa only [hsCI] using hp.coreIncompatible) (by simpa only [hsCP] using hp.corePair)
    (by simpa only [hsCJ] using hp.coreJoint)
  obtain ⟨ND, _hND, hd⟩ := hd (by simpa only [hsD0] using hp.deficitInitial)
    (by simpa only [hsD] using hp.deficit)
  refine ⟨10 + NL + NC + ND + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let F := (pairs G L).image DistinguishedPairWeights.join
  let low := fun I : Finset ℕ ↦ runRelativeNullity L I ≤ L + 2
  let FL := F.filter low
  let FC := F.filter fun I ↦ ¬ low I
  have hdata (I : Finset ℕ) (hI : I ∈ F) :
      I ⊆ G ∧ 3 ≤ I.card ∧ ConnectedWindowFamilies.Connected L I ∧
        (runRelativeNullity L I ≤ L + 2 ∨ RelationCoreWitnesses.Core 4 L I ∧ runRelativeNullity L I ≤ 2 * L) := by
    obtain ⟨pair, hp, rfl⟩ := mem_image.mp hI
    obtain ⟨heG, he, haG, hdep, hprim⟩ := (mem_pairs G L pair).mp hp
    have hpos : ∀ x ∈ pair.1 ∪ pair.2, 0 < x := by
      intro x hx
      have hxN := hG (union_subset heG haG hx)
      have h := (mem_Ico.mp hxN).1
      omega
    exact ⟨union_subset heG haG, size L pair.1 pair.2 he hprim,
      connected L pair.1 pair.2 he hdep hprim, rank_dichotomy L pair.1 pair.2 he hprim hpos⟩
  have hlow : (∑ I ∈ FL, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hl N (by omega) L hband G hG FL
    intro I hI
    obtain ⟨hIF, hcap⟩ := mem_filter.mp hI
    obtain ⟨hIG, hsize, hconn, _⟩ := hdata I hIF
    exact ⟨hIG, hsize, hconn, hcap⟩
  have hcore : (∑ I ∈ FC, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hc N (by omega) L hband G hG FC
    intro I hI
    obtain ⟨hIF, hnot⟩ := mem_filter.mp hI
    obtain ⟨hIG, hsize, hconn, hdich⟩ := hdata I hIF
    have hlarge := hdich.resolve_left hnot
    exact ⟨hIG, hsize, hconn, hlarge⟩
  have hsplit := sum_filter_add_sum_filter_not F low (fun I ↦
    (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|))
  change (∑ I ∈ FL, (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
    (∑ I ∈ FC, (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) = _ at hsplit
  have htotal : (∑ I ∈ F, (2 * u) ^ I.card *
      (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by
    linarith only [hlow, hcore, hsplit]
  have hdef := (AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L u hu.le).trans
    (hd N (by omega) L hband)
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  calc
    _ ≤ 2 * (∑ I ∈ F, (2 * u) ^ I.card *
        (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
          2 * u ^ 2 * AllPairExtensionDeficit.deficit G L u := finite_bound G L hL u hu.le
    _ ≤ (4 + 2 * u ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by
      have hD := mul_le_mul_of_nonneg_left (hdef.trans hpower) (by positivity : 0 ≤ 2 * u ^ 2)
      nlinarith only [htotal, hD]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

/-- In particular, this retains any source-channel or original-window separation restriction. -/
theorem uniform_subfamily (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ P : Finset (Finset ℕ × Finset ℕ),
      P ⊆ pairs G L → mass P L u ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := uniform_bound u C ε hu hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG P hP
  exact (mass_mono P (pairs G L) hP L u hu.le).trans (h N hN L hband G hG)

end PaperP1.CompressedPairMassUnderInputs
