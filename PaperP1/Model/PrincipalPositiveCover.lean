module

public import PaperP1.Model.SourcePairPositiveWeight
public import PaperP1.Model.PrivateChannelPositiveMass
public import PaperP1.Model.PrincipalChannelEdges
public import PaperP1.Model.PrincipalAlignedCover
public import PaperP1.Arithmetic.StrictChannelSourceSeparation
public import PaperP1.Combinatorics.PairSeparation

/-! # The separated positive source sum splits into actual private channels and residual classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalPositiveCover

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SourcePairPositiveWeight
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.PrivateChannelSources

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def separated (N L : ℕ) : Finset (Finset ℕ) :=
  (dyadicBlock N).powersetCard 2 \ ClosePairs.pairs (dyadicBlock N) L

def principal (N H L : ℕ) : Finset (Finset ℕ) :=
  PrivateChannelActivity.pairs N H 2 3 L ∪ PrivateChannelActivity.pairs N H 3 4 L

def residual (N H L : ℕ) : Finset (Finset ℕ) :=
  (separated N L \ principal N H L) ∩ AllAlignedPairs.families N L

theorem ordered_host_sum (G : Finset ℕ) (F : Finset (Finset ℕ)) (L : ℕ) (hF : F ⊆ G.powersetCard 2) :
    (∑ p ∈ PairSubfamilyWeights.hosts G F, weight p.1 p.2 L) = 2 * ∑ e ∈ F, setWeight L e := by
  calc
    _ = ∑ p ∈ PairSubfamilyWeights.hosts G F, setWeight L {p.1, p.2} := by
      apply sum_congr rfl
      intro p hp
      exact (setWeight_pair ((PairSubfamilyWeights.mem_hosts G F p).mp hp).2.2.1 L).symm
    _ = _ := PairSubfamilyWeights.weighted_sum G F hF (setWeight L)

theorem ordered_separated_sum (N L : ℕ) :
    (∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) =
      2 * ∑ e ∈ separated N L, setWeight L e := by
  let G := dyadicBlock N
  have hpartition := PairSeparation.sum_partition G L (fun p ↦ weight p.1 p.2 L)
  have hclose : (∑ p ∈ PairSeparation.closeHosts G L, weight p.1 p.2 L) =
      2 * ∑ e ∈ ClosePairs.pairs G L, setWeight L e :=
    ordered_host_sum G (ClosePairs.pairs G L) L (ClosePairs.subset G L)
  have hall : (∑ p ∈ OrderedPairTuples.pairs G, weight p.1 p.2 L) =
      2 * ∑ e ∈ G.powersetCard 2, setWeight L e := by
    calc
      _ = ∑ p ∈ OrderedPairTuples.pairs G, setWeight L {p.1, p.2} := by
        apply sum_congr rfl
        intro p hp
        exact (setWeight_pair (mem_filter.mp hp).2 L).symm
      _ = _ := OrderedPairTuples.weighted_subsets G (setWeight L)
  have hsets := sum_sdiff (f := setWeight L) (ClosePairs.subset G L)
  rw [hclose, hall] at hpartition
  change _ = 2 * ∑ e ∈ G.powersetCard 2 \ ClosePairs.pairs G L, setWeight L e
  linarith only [hpartition, hsets]

theorem private_pair_not_close {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    {e : Finset ℕ} (he : e ∈ PrivateChannelActivity.pairs N H a b L) :
    e ∉ ClosePairs.pairs (dyadicBlock N) L := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, hu, _hp⟩ := mem_goodSources.mp hxy
  obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (units a b xy.1 xy.2 L).card)
  have hsep := StrictChannelSourceSeparation.source_strictly_separated hN ha hab hcop hlarge u.1 u.2
    (DyadicEndpointPairs.mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hu⟩)
  intro hc
  obtain ⟨x, y, _hx, _hy, hlt, hnear, heq⟩ := ClosePairs.data _ _ _ hc
  have hxm : x ∈ ({xy.1, xy.2} : Finset ℕ) := by rw [heq]; simp
  have hym : y ∈ ({xy.1, xy.2} : Finset ℕ) := by rw [heq]; simp
  simp only [mem_insert, mem_singleton] at hxm hym
  omega

theorem principal_subset_separated {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    principal N H L ⊆ separated N L := by
  intro e he
  rcases mem_union.mp he with h23 | h34
  · exact mem_sdiff.mpr ⟨mem_powersetCard.mpr
      (PrivateChannelActivity.pair_data hN (by decide : 2 < 3) (by omega) h23),
      private_pair_not_close hN (by decide : 0 < 2) (by decide : 2 < 3) (by decide) (by omega) h23⟩
  · exact mem_sdiff.mpr ⟨mem_powersetCard.mpr
      (PrivateChannelActivity.pair_data hN (by decide : 3 < 4) (by omega) h34),
      private_pair_not_close hN (by decide : 0 < 3) (by decide : 3 < 4) (by decide) (by omega) h34⟩

theorem private_mass_eq {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    (∑ e ∈ PrivateChannelActivity.pairs N H a b L, setWeight L e) =
      PrivateChannelPositiveMass.channelWeight N H a b L / 2 := by
  rw [PrivateChannelPositiveMass.channel_weight_twice_forward hN hab hlarge,
    PrivateChannelActivity.pairs, sum_image (PrivateChannelActivity.pair_map_injective hN hab hlarge)]
  have heq : (∑ xy ∈ goodSources N H a b L, setWeight L {xy.1, xy.2}) =
      PrivateChannelPositiveMass.forwardWeight N H a b L := by
    apply sum_congr rfl
    intro xy hxy
    exact setWeight_pair (ne_of_lt (good_sources_order hN hab hlarge hxy)) L
  rw [heq]
  ring

theorem principal_mass_eq {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    2 * (∑ e ∈ principal N H L, setWeight L e) =
      PrivateChannelPositiveMass.channelWeight N H 2 3 L + PrivateChannelPositiveMass.channelWeight N H 3 4 L := by
  rw [principal, sum_union (PrincipalChannelEdges.unordered_disjoint hN hlarge),
    private_mass_eq hN (by decide : 2 < 3) (by omega), private_mass_eq hN (by decide : 3 < 4) (by omega)]
  ring

theorem one_unit_zero {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxy : x ≠ y) (hu : (units a b x y L).Nonempty) (hcard : (units a b x y L).card ≤ 1)
    (hp : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    setWeight L {x, y} = 0 := by
  have hloss := private_loss_eq ha hb hx hy hu hp
  have hz : pairLoss x y L = 0 := by omega
  rw [setWeight_pair hxy, weight, hz, pow_zero, sub_self]

theorem channel_nonzero_cover {N H L a b : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hheight : b ≤ (L + 1) ^ 3)
    {e : Finset ℕ} (he : e ∈ BoundaryAlignedPairs.channel N L a b) (hn : setWeight L e ≠ 0) :
    e ∈ PrivateChannelActivity.pairs N H a b L ∪ NormalizedDefectPairActivity.pairs N H a b L ∪
      AlignedChannelFamilies.zeroFamilies N L := by
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, hx, hy, rfl, hxy, hg⟩ := BoundaryAlignedPairs.data he
  by_cases hu : (units a b x y L).Nonempty
  · by_cases hp : GoodEdgeCompression.PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L)
    · by_cases htwo : 2 ≤ (units a b x y L).card
      · exact mem_union_left _ (mem_union_left _ (mem_image.mpr
          ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, htwo, hp⟩, rfl⟩))
      · exact False.elim (hn (one_unit_zero ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1)
          (hN.trans (mem_Ico.mp hy).1) hxy.ne hu (by omega) hp.private))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr
        ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hu, hp⟩, rfl⟩))
  · exact mem_union_right _ (mem_filter.mpr ⟨heN, x, y, a, b, rfl, hxy, ha, ha.trans hab, hcop,
      by simpa only [max_eq_right hab.le] using hheight, hg,
      Nat.eq_zero_of_not_pos (fun hp ↦ hu (card_pos.mp hp))⟩)

def classes (N H L i : ℕ) : Finset (Finset ℕ) :=
  if i = 0 then BoundaryAlignedPairs.channel N L 1 1 \ ClosePairs.pairs (dyadicBlock N) L else
  if i = 1 then BoundaryAlignedPairs.channel N L 1 2 else
  if i = 2 then NormalizedDefectPairActivity.pairs N H 2 3 L else
  if i = 3 then NormalizedDefectPairActivity.pairs N H 3 4 L else
  if i = 4 then AlignedChannelFamilies.zeroFamilies N L else
    AlignedChannelFamilies.families N L 5

theorem residual_cover {N H L : ℕ} (hN : 2 ≤ N) (hheight : 4 ≤ (L + 1) ^ 3)
    (hlarge : 2 * (L + 1) ^ 4 < N) {e : Finset ℕ} (he : e ∈ residual N H L)
    (hn : setWeight L e ≠ 0) : ∃ i ∈ range 6, e ∈ classes N H L i := by
  obtain ⟨heR, heA⟩ := mem_inter.mp he
  obtain ⟨heS, heP⟩ := mem_sdiff.mp heR
  have hnotclose := (mem_sdiff.mp heS).2
  rcases AllAlignedPairs.classification hlarge heA with h1 | h2 | h23 | h34 | htail
  · exact ⟨0, by decide, by simpa only [classes, ite_true] using mem_sdiff.mpr ⟨h1, hnotclose⟩⟩
  · exact ⟨1, by decide, by simpa only [classes, show ¬(1 : ℕ) = 0 by decide, ite_false, ite_true] using h2⟩
  · have hc := channel_nonzero_cover (H := H) hN (by decide : 0 < 2) (by decide : 2 < 3)
      (by decide) (by omega) h23 hn
    rcases mem_union.mp hc with hc | hz
    · rcases mem_union.mp hc with hp | hb
      · exact False.elim (heP (mem_union_left _ hp))
      · exact ⟨2, by decide, by simpa [classes] using hb⟩
    · exact ⟨4, by decide, by simpa [classes] using hz⟩
  · have hc := channel_nonzero_cover (H := H) hN (by decide : 0 < 3) (by decide : 3 < 4)
      (by decide) hheight h34 hn
    rcases mem_union.mp hc with hc | hz
    · rcases mem_union.mp hc with hp | hb
      · exact False.elim (heP (mem_union_right _ hp))
      · exact ⟨3, by decide, by simpa [classes] using hb⟩
    · exact ⟨4, by decide, by simpa [classes] using hz⟩
  · exact ⟨5, by decide, by simpa [classes] using htail⟩

theorem finite_weight_cover (F : Finset (Finset ℕ)) (I : Finset ℕ)
    (A : ℕ → Finset (Finset ℕ)) (w : Finset ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hcover : ∀ e ∈ F, w e ≠ 0 → ∃ i ∈ I, e ∈ A i) :
    (∑ e ∈ F, w e) ≤ ∑ i ∈ I, ∑ e ∈ A i, w e := by
  let P := F.filter fun e ↦ w e ≠ 0
  have hsum : (∑ e ∈ P, w e) = ∑ e ∈ F, w e := by
    apply sum_subset (filter_subset _ _)
    intro e he hn
    exact not_ne_iff.mp (fun hp ↦ hn (mem_filter.mpr ⟨he, hp⟩))
  have hsub : P ⊆ I.biUnion A := by
    intro e he
    obtain ⟨i, hi, heA⟩ := hcover e (mem_filter.mp he).1 (mem_filter.mp he).2
    exact mem_biUnion.mpr ⟨i, hi, heA⟩
  rw [← hsum]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ hw e)).trans
    (GraphStarWeights.sum_biUnion_le_nonneg I A w hw)

theorem finite_residual_bound {N H L : ℕ} (hN : 2 ≤ N) (hheight : 4 ≤ (L + 1) ^ 3)
    (hlarge : 2 * (L + 1) ^ 4 < N) :
    (∑ e ∈ residual N H L, setWeight L e) ≤
      (∑ e ∈ BoundaryAlignedPairs.channel N L 1 1 \ ClosePairs.pairs (dyadicBlock N) L, setWeight L e) +
      (∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, setWeight L e) +
      (∑ e ∈ NormalizedDefectPairActivity.pairs N H 2 3 L, setWeight L e) +
      (∑ e ∈ NormalizedDefectPairActivity.pairs N H 3 4 L, setWeight L e) +
      (∑ e ∈ AlignedChannelFamilies.zeroFamilies N L, setWeight L e) +
      (∑ e ∈ AlignedChannelFamilies.families N L 5, setWeight L e) := by
  have h := finite_weight_cover (residual N H L) (range 6) (classes N H L) (setWeight L)
    (setWeight_nonneg L) (fun _ he hn ↦ residual_cover hN hheight hlarge he hn)
  simpa only [sum_range_succ, sum_range_zero, classes, ite_true, ite_false, Nat.reduceEqDiff, zero_add] using h

end PaperP1.PrincipalPositiveCover
