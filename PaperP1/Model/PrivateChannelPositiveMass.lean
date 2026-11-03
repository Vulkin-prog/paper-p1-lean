module

public import PaperP1.Model.SourcePairPositiveWeight
public import PaperP1.Model.UnsignedUnitFourierAggregate
public import PaperP1.Model.PrivateChannelRemoval

/-! # Actual positive arithmetic mass of a private rational channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelPositiveMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.NormalizedUnitCount PaperP1.PrivateChannelSources PaperP1.NormalizedDefectSources
  PaperP1.UnsignedUnitFourierAggregate PaperP1.SourcePairPositiveWeight

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def forwardWeight (N H a b L : ℕ) : ℝ :=
  ∑ xy ∈ goodSources N H a b L, weight xy.1 xy.2 L

def channelWeight (N H a b L : ℕ) : ℝ :=
  ∑ xy ∈ channelSources N H a b L, weight xy.1 xy.2 L

theorem good_source_weight {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    {xy : ℕ × ℕ} (hxy : xy ∈ goodSources N H a b L) :
    weight xy.1 xy.2 L = unitWeight a b xy.1 xy.2 L := by
  unfold weight unitWeight
  rw [good_source_loss hN ha hb hxy]

theorem channel_weight_twice_forward {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) : channelWeight N H a b L = 2 * forwardWeight N H a b L := by
  unfold channelWeight channelSources
  rw [sum_union (orientation_disjoint hN hab hlarge), sum_image]
  · have heq : (∑ xy ∈ goodSources N H a b L, weight xy.2 xy.1 L) = forwardWeight N H a b L := by
      unfold forwardWeight
      apply sum_congr rfl
      intro xy _
      exact weight_comm _ _ _
    change forwardWeight N H a b L + (∑ xy ∈ goodSources N H a b L, weight xy.2 xy.1 L) = _
    rw [heq]
    ring
  · intro xy _ uv _ heq
    have h := congrArg Prod.swap heq
    simpa using h

theorem unit_sum_partition (N H a b L : ℕ) :
    (∑ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), unitWeight a b xy.1 xy.2 L) =
      (∑ xy ∈ goodSources N H a b L, unitWeight a b xy.1 xy.2 L) +
      (∑ xy ∈ badSources N H a b L, unitWeight a b xy.1 xy.2 L) := by
  let D := (dyadicBlock N) ×ˢ (dyadicBlock N)
  let f : ℕ × ℕ → ℝ := fun xy ↦ unitWeight a b xy.1 xy.2 L
  have hfilter (T : Finset (ℕ × ℕ)) (hT : T ⊆ D) : D.filter (fun xy ↦ xy ∈ T) = T := by
    ext xy
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hT h, h⟩⟩
  have hgood : D.filter (fun xy ↦ xy ∈ goodSources N H a b L) = goodSources N H a b L :=
    hfilter _ (by intro xy hxy; have hg := mem_goodSources.mp hxy; exact mem_product.mpr ⟨hg.1, hg.2.1⟩)
  have hbad : D.filter (fun xy ↦ xy ∈ badSources N H a b L) = badSources N H a b L :=
    hfilter _ (by intro xy hxy; exact (mem_filter.mp hxy).1)
  have hpoint (xy : ℕ × ℕ) (hxy : xy ∈ D) :
      f xy = (if xy ∈ goodSources N H a b L then f xy else 0) +
        (if xy ∈ badSources N H a b L then f xy else 0) := by
    by_cases hc : 2 ≤ (units a b xy.1 xy.2 L).card
    · have hb := mem_product.mp hxy
      by_cases hp : GoodEdgeCompression.PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b xy.1 xy.2 L)
      · have hg : xy ∈ goodSources N H a b L := mem_goodSources.mpr ⟨hb.1, hb.2, hc, hp⟩
        have hn : xy ∉ badSources N H a b L := fun h ↦ (mem_filter.mp h).2.2 hp
        rw [ite_eq_left hg, ite_eq_right hn, add_zero]
      · have hg : xy ∉ goodSources N H a b L := fun h ↦ hp (mem_goodSources.mp h).2.2.2
        have hn : xy ∈ badSources N H a b L := mem_filter.mpr ⟨hxy, card_pos.mp (by omega), hp⟩
        rw [ite_eq_right hg, ite_eq_left hn, zero_add]
    · have hz : f xy = 0 := unitWeight_zero_of_card_le_one (by omega)
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

theorem bad_unit_sum_bound {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    (∑ xy ∈ badSources N H a b L, unitWeight a b xy.1 xy.2 L) ≤
      ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  calc
    _ ≤ ∑ _xy ∈ badSources N H a b L, (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
      apply sum_le_sum
      intro xy hxy
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hxy).1
      exact unitWeight_le_rpow ha hb hab (by have := (mem_Ico.mp hx).1; omega)
        (by have := (mem_Ico.mp hy).1; omega)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem exact_decomposition {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    channelWeight N H a b L =
      2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) -
        2 * (∑ xy ∈ badSources N H a b L, unitWeight a b xy.1 xy.2 L) := by
  have hAll : (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) =
      (∑ xy ∈ goodSources N H a b L, unitWeight a b xy.1 xy.2 L) +
      (∑ xy ∈ badSources N H a b L, unitWeight a b xy.1 xy.2 L) :=
    (sum_product _ _ (fun xy : ℕ × ℕ ↦ unitWeight a b xy.1 xy.2 L)).symm.trans
      (unit_sum_partition N H a b L)
  have hgood : forwardWeight N H a b L = ∑ xy ∈ goodSources N H a b L, unitWeight a b xy.1 xy.2 L :=
    sum_congr rfl fun _ hxy ↦ good_source_weight hN ha (ha.trans hab) hxy
  rw [channel_weight_twice_forward hN hab hlarge, hgood, hAll]
  ring

theorem finite_weight_error {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    |channelWeight N H a b L -
      (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ)| ≤
      6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) +
        2 * ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  let E : ℝ := 2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) -
    (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ)
  let V : ℝ := ∑ xy ∈ badSources N H a b L, unitWeight a b xy.1 xy.2 L
  have hE := finite_unsigned_sum_error hN ha hab hinterior hcop hlarge
  have hV := bad_unit_sum_bound (H := H) (L := L) hN ha (ha.trans hab) hcop
  have hVpos : 0 ≤ V := sum_nonneg fun xy _ ↦ unitWeight_nonneg a b xy.1 xy.2 L
  have heq : channelWeight N H a b L -
      (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) = E - 2 * V := by
    rw [exact_decomposition hN ha hab hlarge]
    dsimp only [E, V]
    ring
  rw [heq]
  have h := abs_sub E (2 * V)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * V)] at h
  nlinarith only [h, hE, hV]

end PaperP1.PrivateChannelPositiveMass
