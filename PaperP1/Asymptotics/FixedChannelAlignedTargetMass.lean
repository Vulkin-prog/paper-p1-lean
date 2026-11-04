module

public import PaperP1.Asymptotics.AlignedTargetRank
public import PaperP1.Asymptotics.BinaryRankPowers
public import PaperP1.Asymptotics.UnitChannelPairWeights
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Arithmetic.FixedChannelGammaLower
public import PaperP1.Model.PairTargetQuotientProbability
public import PaperP1.Model.GoodEdgePositivePalm

/-! # Aligned targets retain the literal fixed-channel gamma exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelAlignedTargetMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedChannelGamma PaperP1.DyadicEndpointPairs PaperP1.CompressedSourceBlocks

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ((ℕ × ℕ) × ℕ) :=
  ((sourcePairs N a b L i j) ×ˢ dyadicBlock N).filter fun p ↦
    p.2 ≠ p.1.1 ∧ p.2 ≠ p.1.2 ∧
      CompressedTargetAlignment.Aligned b (anchor b L i p.1) p.2 L

def mass (N a b L : ℕ) (i j : Fin (L + 1)) : ℝ :=
  ∑ p ∈ points N a b L i j, infiniteJointMoment L {p.1.1, p.1.2, p.2}

def channelMass (N a b L : ℕ) : ℝ :=
  ∑ ij : Fin (L + 1) × Fin (L + 1), mass N a b L ij.1 ij.2

theorem uniform_polynomial (C A ε : ℝ) (hA : 0 ≤ A) (k : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      A * ((L + 1 : ℕ) : ℝ) ^ k ≤ (N : ℝ) ^ ε := by
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le A k ε hε
  refine ⟨max NS NP, ?_⟩
  intro N hN L hband
  have hh := hp N (by omega) L (hs N (by omega) L hband).2
  rw [abs_of_nonneg (mul_nonneg hA (by positivity))] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem uniform_point {a b : ℕ} (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ i j : Fin (L + 1), ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ dyadicBlock N,
      z ≠ xy.1 → z ≠ xy.2 →
      CompressedTargetAlignment.Aligned b (anchor b L i xy) z L →
      xy ∉ AlignedTargetRank.endpointSources N a b L →
      infiniteJointMoment L {xy.1, xy.2, z} ≤
        infiniteJointMoment L {xy.1, xy.2} * (N : ℝ) ^ (-1 + gammaReal a b + ε) := by
  let δ := min (ε / 2) (1 / 12)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδq : δ ≤ 1 / 12 := min_le_right _ _
  have hγ := gammaReal_le_two_thirds hcop hb
  have hα : 0 ≤ 1 - gammaReal a b - δ := by linarith only [hγ, hδq]
  obtain ⟨NR, hr⟩ := AlignedTargetRank.uniform_core C δ hδ ha hb hcop hab b
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, haB⟩ := HalfCountSchedule.factor_absorption
    (BinaryRankPowers.constant C (1 - gammaReal a b - δ) 0)
    (-1 + gammaReal a b + δ) (ε - δ) (by linarith only [hδε, hε])
  refine ⟨max 10 (max NR (max NG NA)), by omega, ?_⟩
  intro N hN L hband i j xy hxy z hz hzx hzy halign haway
  by_cases hq : 0 < infiniteJointMoment L {xy.1, xy.2, z}
  · obtain ⟨hx, hy, hu⟩ := mem_sourcePairs.mp hxy
    obtain ⟨t, _ht, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
      (by have hh := (mem_Ico.mp hx).1; omega) i j hu
    have hanchor : anchor b L i xy = a * b * t := by dsimp [anchor]; rw [hbaseX]; ring
    have htarget : z ∈ AlignedTargetRank.targets b N a b t L := by
      apply mem_filter.mpr
      exact ⟨hz, by simpa only [hanchor] using halign⟩
    have hsep := GoodEdgePositivePalm.separated_of_positive_joint L
      (by have hh := hg N (by omega) L hband; omega) {xy.1, xy.2, z} hq
    have hsepX := hsep xy.1 (by simp) z (by simp) hzx.symm
    have hsepY := hsep xy.2 (by simp) z (by simp) hzy.symm
    have hrank := (hr N (by omega) L hband).2 xy.1 xy.2 t hx hy i j hbaseX hbaseY
    have hdef := hrank.2 z htarget hsepX hsepY haway ∅ (empty_subset _)
    have hzpos : 0 < z := by have hh := (mem_Ico.mp hz).1; omega
    have hadd := PairTargetQuotientProbability.deficiency_add (x := xy.1) (y := xy.2) (L := L) hzpos
    have haddR : (TargetWindowRank.deficiency ∅ xy.1 xy.2 z L : ℝ) +
        PairTargetQuotientProbability.addedRank xy.1 xy.2 z L = L := by exact_mod_cast hadd
    have hR : (1 - gammaReal a b - δ) * L - 0 ≤
        (PairTargetQuotientProbability.addedRank xy.1 xy.2 z L : ℝ) := by nlinarith only [hdef, haddR]
    have hp := BinaryRankPowers.upper (by omega : 2 ≤ N) hα hband hR
    rw [show -(1 - gammaReal a b - δ) = -1 + gammaReal a b + δ by ring] at hp
    have hpow : (2 ^ PairTargetQuotientProbability.addedRank xy.1 xy.2 z L : ℝ)⁻¹ ≤
        (N : ℝ) ^ (-1 + gammaReal a b + ε) := hp.trans (by
      simpa only [show (-1 + gammaReal a b + δ) + (ε - δ) = -1 + gammaReal a b + ε by ring] using haB N (by omega))
    exact (PairTargetQuotientProbability.joint_upper
      (by have hh := hg N (by omega) L hband; omega) hzx hzy).trans
      (mul_le_mul_of_nonneg_left hpow (infiniteJointMoment_nonneg L _))
  · exact (not_lt.mp hq).trans (mul_nonneg (infiniteJointMoment_nonneg L _) (by positivity))

def targetSet (N _a b L : ℕ) (i : Fin (L + 1)) (xy : ℕ × ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun z ↦ z ≠ xy.1 ∧ z ≠ xy.2 ∧
    CompressedTargetAlignment.Aligned b (anchor b L i xy) z L

theorem iterated_mass (N a b L : ℕ) (i j : Fin (L + 1)) :
    mass N a b L i j = ∑ xy ∈ sourcePairs N a b L i j,
      ∑ z ∈ targetSet N a b L i xy, infiniteJointMoment L {xy.1, xy.2, z} := by
  simp only [mass, points, sum_filter, sum_product, targetSet]

theorem target_card {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hcop : a.Coprime b)
    {ε : ℝ} (hcore : AlignedTargetRank.Conclusion b N a b L ε)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    (targetSet N a b L i xy).card ≤ 6 * a * (L + 1) ^ 15 := by
  obtain ⟨hx, hy, hu⟩ := mem_sourcePairs.mp hxy
  obtain ⟨t, _ht, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
    (hN.trans (mem_Ico.mp hx).1) i j hu
  have hanchor : anchor b L i xy = a * b * t := by dsimp [anchor]; rw [hbaseX]; ring
  have hsub : targetSet N a b L i xy ⊆ AlignedTargetRank.targets b N a b t L := by
    intro z hz
    obtain ⟨hzN, _hzx, _hzy, hzA⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hzN, by simpa only [hanchor] using hzA⟩
  exact (card_le_card hsub).trans (hcore.2 xy.1 xy.2 t hx hy i j hbaseX hbaseY).1

theorem finite_bound (N a b L : ℕ) (i j : Fin (L + 1)) (Z Q T : ℝ)
    (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hcard : ∀ xy ∈ sourcePairs N a b L i j, (targetSet N a b L i xy).card ≤ Z)
    (hsource : ∀ xy ∈ sourcePairs N a b L i j, infiniteJointMoment L {xy.1, xy.2} ≤ Q)
    (hpoint : ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ targetSet N a b L i xy,
      xy ∉ AlignedTargetRank.endpointSources N a b L →
      infiniteJointMoment L {xy.1, xy.2, z} ≤ infiniteJointMoment L {xy.1, xy.2} * T) :
    mass N a b L i j ≤ (sourcePairs N a b L i j).card * Z * Q * T +
      (AlignedTargetRank.endpointSources N a b L).card * Z * Q := by
  let E := AlignedTargetRank.endpointSources N a b L
  let S := sourcePairs N a b L i j
  have hinner (xy : ℕ × ℕ) (hxy : xy ∈ S) :
      (∑ z ∈ targetSet N a b L i xy, infiniteJointMoment L {xy.1, xy.2, z}) ≤
        Z * Q * T + if xy ∈ E then Z * Q else 0 := by
    have hsum : (∑ z ∈ targetSet N a b L i xy, infiniteJointMoment L {xy.1, xy.2, z}) ≤
        (targetSet N a b L i xy).card * (Q * T + if xy ∈ E then Q else 0) := by
      calc
        _ ≤ ∑ _z ∈ targetSet N a b L i xy, (Q * T + if xy ∈ E then Q else 0) := by
          apply sum_le_sum
          intro z hz
          by_cases hbad : xy ∈ E
          · rw [ite_eq_left hbad]
            have hsub : ({xy.1, xy.2} : Finset ℕ) ⊆ {xy.1, xy.2, z} := by
              intro n hn
              simp only [mem_insert, mem_singleton] at hn ⊢
              tauto
            have hh := (MissingBlockProbabilities.infiniteJointMoment_antitone L hsub).trans (hsource xy hxy)
            nlinarith only [hh, mul_nonneg hQ hT]
          · rw [ite_eq_right hbad, add_zero]
            exact (hpoint xy hxy z hz hbad).trans (mul_le_mul_of_nonneg_right (hsource xy hxy) hT)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have hright : 0 ≤ Q * T + if xy ∈ E then Q else 0 := by split_ifs <;> positivity
    have hh := hsum.trans (mul_le_mul_of_nonneg_right (hcard xy hxy) hright)
    by_cases hbad : xy ∈ E <;> simpa [hbad, mul_add, mul_assoc] using hh
  rw [iterated_mass]
  have hsum := sum_le_sum hinner
  have hfilter : ((S.filter fun xy ↦ xy ∈ E).card : ℝ) ≤ E.card := by
    exact_mod_cast card_le_card (show S.filter (fun xy ↦ xy ∈ E) ⊆ E from fun _ h ↦ (mem_filter.mp h).2)
  calc
    _ ≤ ∑ xy ∈ S, (Z * Q * T + if xy ∈ E then Z * Q else 0) := hsum
    _ = (S.card : ℝ) * (Z * Q * T) + ((S.filter fun xy ↦ xy ∈ E).card : ℝ) * (Z * Q) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) * (Z * Q * T) + (E.card : ℝ) * (Z * Q) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hfilter (mul_nonneg hZ hQ))
    _ = _ := by dsimp only [S, E]; ring

end PaperP1.FixedChannelAlignedTargetMass
