module

public import PaperP1.Model.PrivateChannelActivity

/-! # Exact relative nullity, regularity and probability cap of a private channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.SubspaceFamilyRank
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateChannelSources
  PaperP1.PrivateChannelActivity PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount
  PaperP1.PrivateUnitCovariance

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem source_nullity_eq {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {xy : ℕ × ℕ} (hxy : xy ∈ goodSources N H a b L) :
    runRelativeNullity L {xy.1, xy.2} = (units a b xy.1 xy.2 L).card - 1 := by
  obtain ⟨hx, hy, hu, hprivate⟩ := mem_goodSources.mp hxy
  have hx2 := hN.trans (mem_Ico.mp hx).1
  have hy2 := hN.trans (mem_Ico.mp hy).1
  have hxyne := ne_of_lt (good_sources_order hN hab hlarge hxy)
  obtain ⟨hrx, hry⟩ := CompressionRank.private_local_ranks ha (ha.trans hab) hx2 hy2 hprivate.private
  have hrank := rank_union ha (ha.trans hab) hx2 hy2
    (CompressionRank.units_intersection_nonempty (card_pos.mp (by omega))) hprivate.private
  have hcard := card_union_add_card_inter (normalized b xy.1 L) (normalized a xy.2 L)
  rw [card_normalized (ha.trans hab) (by omega), card_normalized ha (by omega),
    normalized_intersection_card ha (ha.trans hab) (by omega) (by omega)] at hcard
  change (union a b xy.1 xy.2 L).card + (units a b xy.1 xy.2 L).card = (L + 1) + (L + 1) at hcard
  have hdim := rank_add_nullity_on (fun z ↦ squareClassSpace z L) {xy.1, xy.2}
  rw [sum_pair hxyne, hrx, hry] at hdim
  change Module.finrank F₂ (span (fun z ↦ squareClassSpace z L) {xy.1, xy.2}) +
    runRelativeNullity L {xy.1, xy.2} = L + L at hdim
  rw [RetainedNullity.span_pair, hrank] at hdim
  change (union a b xy.1 xy.2 L).card - 1 + runRelativeNullity L {xy.1, xy.2} = L + L at hdim
  have hU : 1 ≤ (union a b xy.1 xy.2 L).card := card_pos.mpr
    ((normalized_nonempty b xy.1 L).mono subset_union_left)
  omega

theorem nullity_positive {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {e : Finset ℕ} (he : e ∈ pairs N H a b L) :
    0 < runRelativeNullity L e := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  rw [source_nullity_eq hN ha hab hlarge hxy]
  have h := (mem_goodSources.mp hxy).2.2.1
  omega

theorem nullity_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    {e : Finset ℕ} (he : e ∈ pairs N H a b L) :
    (runRelativeNullity L e : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  rw [source_nullity_eq hN ha hab hlarge hxy]
  obtain ⟨hx, hy, _, _⟩ := mem_goodSources.mp hxy
  exact UnitFourierWeight.unit_kernel_rank_bound ha (ha.trans hab) hcop
    (by have h := (mem_Ico.mp hx).1; omega) (by have h := (mem_Ico.mp hy).1; omega)

theorem regular {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    {e : Finset ℕ} (he : e ∈ pairs N H a b L) : e ⊆ RegularStarts.regularStarts N L := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
  obtain ⟨hrx, hry⟩ := CompressionRank.private_local_ranks ha (ha.trans hab)
    (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1) hprivate.private
  exact insert_subset_iff.mpr ⟨RegularStarts.mem_regularStarts.mpr ⟨hx, hrx⟩,
    singleton_subset_iff.mpr (RegularStarts.mem_regularStarts.mpr ⟨hy, hry⟩)⟩

theorem joint_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L)
    {e : Finset ℕ} (he : e ∈ pairs N H a b L) :
    infiniteJointMoment L e ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
  rw [private_pair_mass ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
    (hN.trans (mem_Ico.mp hy).1) (ne_of_lt (good_sources_order hN hab hlarge hxy)) hL hprivate.private]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ (2 ^ ((units a b xy.1 xy.2 L).card - 1) : ℝ) := by
      have h := (le_abs_self (signedUnitSum a b xy.1 xy.2 L)).trans
        (UnitFourierWeight.abs_signed_unit_sum a b xy.1 xy.2 L)
      linarith only [h]
    _ = (2 : ℝ) ^ (((units a b xy.1 xy.2 L).card - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (UnitFourierWeight.unit_kernel_rank_bound ha (ha.trans hab) hcop
        (by have h := (mem_Ico.mp hx).1; omega) (by have h := (mem_Ico.mp hy).1; omega))

end PaperP1.PrivateChannelRank
