module

public import PaperP1.Model.PrivateChannelSources

/-! # Exact deletion of nonprivate rational-unit terms and their literal weight bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelRemoval

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.GoodEdgeCompression PaperP1.NormalizedDefectSources PaperP1.PrivateUnitCovariance
  PaperP1.PrivateChannelSources PaperP1.UnitFourierWeight

local instance privateChannelRemovalPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem signed_sum_partition (N H a b L : ℕ) :
    (∑ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), signedUnitSum a b xy.1 xy.2 L) =
      (∑ xy ∈ goodSources N H a b L, signedUnitSum a b xy.1 xy.2 L) +
      (∑ xy ∈ badSources N H a b L, signedUnitSum a b xy.1 xy.2 L) := by
  let D := (dyadicBlock N) ×ˢ (dyadicBlock N)
  let f : ℕ × ℕ → ℝ := fun xy ↦ signedUnitSum a b xy.1 xy.2 L
  have hfilter (T : Finset (ℕ × ℕ)) (hT : T ⊆ D) : D.filter (fun xy ↦ xy ∈ T) = T := by
    ext xy
    simp only [mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨hT h, h⟩
  have hgood : D.filter (fun xy ↦ xy ∈ goodSources N H a b L) = goodSources N H a b L :=
    hfilter _ (by intro xy hxy; have hg := mem_goodSources.mp hxy; exact mem_product.mpr ⟨hg.1, hg.2.1⟩)
  have hbad : D.filter (fun xy ↦ xy ∈ badSources N H a b L) = badSources N H a b L :=
    hfilter _ (by intro xy hxy; exact (mem_filter.mp hxy).1)
  have hpoint (xy : ℕ × ℕ) (hxy : xy ∈ D) :
      f xy = (if xy ∈ goodSources N H a b L then f xy else 0) +
        (if xy ∈ badSources N H a b L then f xy else 0) := by
    by_cases hc : 2 ≤ (units a b xy.1 xy.2 L).card
    · have hb := mem_product.mp hxy
      by_cases hp : PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b xy.1 xy.2 L)
      · have hg : xy ∈ goodSources N H a b L := mem_goodSources.mpr ⟨hb.1, hb.2, hc, hp⟩
        have hn : xy ∉ badSources N H a b L := fun h ↦ (mem_filter.mp h).2.2 hp
        rw [ite_eq_left hg, ite_eq_right hn, add_zero]
      · have hg : xy ∉ goodSources N H a b L := fun h ↦ hp (mem_goodSources.mp h).2.2.2
        have hn : xy ∈ badSources N H a b L := mem_filter.mpr ⟨hxy, card_pos.mp (by omega), hp⟩
        rw [ite_eq_right hg, ite_eq_left hn, zero_add]
    · have hz : f xy = 0 := signed_unit_sum_zero_of_card_le_one (by omega)
      rw [hz]
      simp only [ite_self, add_zero]
  change (∑ xy ∈ D, f xy) = _
  calc
    _ = ∑ xy ∈ D, ((if xy ∈ goodSources N H a b L then f xy else 0) +
        (if xy ∈ badSources N H a b L then f xy else 0)) := sum_congr rfl hpoint
    _ = (∑ xy ∈ D.filter (fun xy ↦ xy ∈ goodSources N H a b L), f xy) +
        (∑ xy ∈ D.filter (fun xy ↦ xy ∈ badSources N H a b L), f xy) := by
      rw [sum_add_distrib, sum_filter, sum_filter]
    _ = _ := by rw [hgood, hbad]

theorem bad_signed_sum_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    |∑ xy ∈ badSources N H a b L, signedUnitSum a b xy.1 xy.2 L| ≤
      ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  calc
    _ ≤ ∑ xy ∈ badSources N H a b L, |signedUnitSum a b xy.1 xy.2 L| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _xy ∈ badSources N H a b L, (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
      apply sum_le_sum
      intro xy hxy
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hxy).1
      exact abs_signed_unit_sum_le_rpow ha hb hab (by have := (mem_Ico.mp hx).1; omega)
        (by have := (mem_Ico.mp hy).1; omega)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end PaperP1.PrivateChannelRemoval
