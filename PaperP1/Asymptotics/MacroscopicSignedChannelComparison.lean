module

public import PaperP1.Model.ActualAffinePairWeight
public import PaperP1.Asymptotics.MacroscopicFixedChannelComparison
public import PaperP1.Model.UnitFourierWeight

/-! # The actual affine phase is compared to the actual signed rational-unit code

Outside the literal nonprivate set, private covariance identifies the two
weights exactly. Both exceptional weights are bounded without assuming
that their compatibility bits agree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicSignedChannelComparison

open Finset PaperP1.Arithmetic PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicKernelExceptionHosts
  PaperP1.MacroscopicFixedChannelComparison PaperP1.PrivateUnitCovariance

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_error (C δ : ℝ) (hδ : 0 < δ) (Q q : ℕ) (hq : 0 < q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → a.Coprime b →
      q ≤ b → b ≤ Q → ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ a b L →
      (∀ xy ∈ E, xy.1 ≠ xy.2) →
      (∑ xy ∈ E, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L - signedUnitSum a b xy.1 xy.2 L|) ≤
        (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MN, hN⟩ := nonprivate_count C Q (ε / 4) (by positivity)
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicRelationPowers.uniform_channel C δ hδ q hq (ε / 4) (by positivity)
  obtain ⟨MU, hU⟩ := PaperP1.MacroscopicRelationPowers.uniform_rational_units C q hq (ε / 4) (by positivity)
  obtain ⟨MG, hG⟩ := uniform_geometry C δ (max Q 2) hδ
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2
    (1 / 2 + 1 / (q : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MN (max MR (max MU (max MG MF))), ?_⟩
  intro M hM L a b hcrit ha hab hcop hqb hbQ E hE hne
  have hm2 : 2 ≤ M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let S := E ∩ nonprivatePairs M δ (cutoff Q L) a b L
  have hsupp : (∑ xy ∈ E, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L - signedUnitSum a b xy.1 xy.2 L|) =
      ∑ xy ∈ S, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L - signedUnitSum a b xy.1 xy.2 L| := by
    symm
    apply sum_subset inter_subset_left
    intro xy hxy hnS
    obtain ⟨hblock, hg⟩ := mem_filter.mp (hE hxy)
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have hgeom := (hG M (by omega) L hcrit xy.1 hx).1
    have hp : PaperP1.GoodEdgeCompression.PrivateAbove (cutoff Q L : ℝ)
        (PaperP1.NormalizedWindowSets.union a b xy.1 xy.2 L) := by
      by_contra hbad
      exact hnS (mem_inter.mpr ⟨hxy, mem_filter.mpr ⟨hblock, hg, hbad⟩⟩)
    rw [PaperP1.ActualAffinePairWeight.private_weight_eq_units ha (ha.trans_le hab)
      (starts_pos hm2 hδ hx) (starts_pos hm2 hδ hy) (hne xy hxy) (by omega) hp.private, sub_self, abs_zero]
  have hpoint : ∀ xy ∈ S, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L - signedUnitSum a b xy.1 xy.2 L| ≤
      2 * (M : ℝ) ^ (1 / (q : ℝ) + ε / 4) := by
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp (hE (mem_inter.mp hxy).1)
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    have hx2 := starts_pos hm2 hδ hx
    have hy2 := starts_pos hm2 hδ hy
    have hwidth := (hG M (by omega) L hcrit xy.1 hx).1
    have hQ : Q ≤ L + 1 := (le_max_left Q 2).trans hwidth
    have hheight : b ≤ (L + 1) ^ 3 := hbQ.trans (hQ.trans (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0)))
    have hp := hR M (by omega) L a b xy.1 xy.2 hcrit ha hab hcop hqb hheight hx hy hg
    have hu := hU M (by omega) L a b xy.1 xy.2 hcrit ha (ha.trans_le hab) hcop hqb (by omega) (by omega)
    have hfull := (PaperP1.ActualAffinePairWeight.abs_weight_le (by omega : 0 < xy.1) (by omega : 0 < xy.2)
      (by omega : 0 < L)).trans hp
    have hrat := (PaperP1.UnitFourierWeight.abs_signed_unit_sum a b xy.1 xy.2 L).trans
      ((sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans hu)
    have ht := abs_sub_le (PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L) 0 (signedUnitSum a b xy.1 xy.2 L)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (by linarith only [hfull, hrat])
  have hc : (S.card : ℝ) ≤ (M : ℝ) ^ (1 / 2 + ε / 4) := by
    have hsub : S ⊆ nonprivatePairs M δ (cutoff Q L) a b L := inter_subset_right
    have hcard : (S.card : ℝ) ≤ (nonprivatePairs M δ (cutoff Q L) a b L).card := by exact_mod_cast card_le_card hsub
    exact hcard.trans (hN M (by omega) δ hδ L a b hcrit ha hab hbQ)
  rw [hsupp]
  calc
    _ ≤ ∑ _xy ∈ S, 2 * (M : ℝ) ^ (1 / (q : ℝ) + ε / 4) := sum_le_sum hpoint
    _ = S.card * (2 * (M : ℝ) ^ (1 / (q : ℝ) + ε / 4)) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) ^ (1 / 2 + ε / 4) * (2 * (M : ℝ) ^ (1 / (q : ℝ) + ε / 4)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 * (M : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hm]
      congr 2
      ring
    _ ≤ (M : ℝ) ^ ((1 / 2 + 1 / (q : ℝ) + ε / 2) + ε / 2) := hF M (by omega)
    _ = _ := by congr 1; ring

theorem height_two (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      ∀ E : Finset (ℕ × ℕ), E ⊆ channelPairs M δ 1 2 L → (∀ xy ∈ E, xy.1 ≠ xy.2) →
      (∑ xy ∈ E, |PaperP1.ActualAffinePairWeight.weight xy.1 xy.2 L - signedUnitSum 1 2 xy.1 xy.2 L|) ≤
        (M : ℝ) ^ (1 + ε) := by
  obtain ⟨M₀, h⟩ := uniform_error C δ hδ 2 2 (by omega) ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit E hE hne
  simpa only [Nat.cast_ofNat, show (1 : ℝ) / 2 + 1 / (2 : ℝ) + ε = 1 + ε by ring] using
    h M hM L 1 2 hcrit (by omega) (by omega) (by norm_num) (by omega) (by omega) E hE hne

end PaperP1.MacroscopicSignedChannelComparison
