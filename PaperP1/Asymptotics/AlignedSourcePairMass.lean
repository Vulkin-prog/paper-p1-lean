module

public import PaperP1.Asymptotics.AlignedSourcePairPowers
public import PaperP1.Asymptotics.OriginalPairHosts
public import PaperP1.Model.SourcePairPositiveWeight
public import PaperP1.Model.BoundaryAlignedPairs
public import PaperP1.Combinatorics.PairSubfamilyWeights

/-! # Positive source mass of the high, zero-unit and boundary aligned populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedSourcePairMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SourcePairPositiveWeight
  PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_support_bound {N L : ℕ} (F : Finset (ℕ × ℕ)) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N)
    (hpoint : ∀ p ∈ F, weight p.1 p.2 L ≤ K) :
    (∑ p ∈ F, weight p.1 p.2 L) ≤ ((PairHostCover.hosts N L).card : ℝ) * K := by
  let P := F.filter fun p ↦ 0 < pairLoss p.1 p.2 L
  have hPF : P ⊆ F := filter_subset _ _
  have hsum : (∑ p ∈ P, weight p.1 p.2 L) = ∑ p ∈ F, weight p.1 p.2 L := by
    apply sum_subset hPF
    intro p hpF hpP
    have hz : pairLoss p.1 p.2 L = 0 := Nat.eq_zero_of_not_pos
      (fun hp ↦ hpP (mem_filter.mpr ⟨hpF, hp⟩))
    simp only [weight, hz, pow_zero, sub_self]
  have hsub : P ⊆ PairHostCover.hosts N L := by
    intro p hp
    exact mem_filter.mpr ⟨mem_product.mpr (hF p (hPF hp)), (mem_filter.mp hp).2⟩
  rw [← hsum]
  calc
    _ ≤ ∑ _p ∈ P, K := sum_le_sum fun p hp ↦ hpoint p (hPF hp)
    _ = (P.card : ℝ) * K := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) hK

theorem finite_set_support_bound {N L : ℕ} (F : Finset (Finset ℕ)) (K : ℝ) (hK : 0 ≤ K)
    (hF : F ⊆ (dyadicBlock N).powersetCard 2) (hpoint : ∀ e ∈ F, setWeight L e ≤ K) :
    (∑ e ∈ F, setWeight L e) ≤ ((PairHostCover.hosts N L).card : ℝ) * K := by
  let S := PairSubfamilyWeights.hosts (dyadicBlock N) F
  have hcap : ∀ p ∈ S, weight p.1 p.2 L ≤ K := by
    intro p hp
    have hd := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp
    rw [← setWeight_pair hd.2.2.1]
    exact hpoint _ hd.2.2.2
  have hordered := finite_support_bound S K hK
    (fun p hp ↦ by have hd := (PairSubfamilyWeights.mem_hosts _ _ p).mp hp; exact ⟨hd.1, hd.2.1⟩) hcap
  have heq : (∑ p ∈ S, weight p.1 p.2 L) = 2 * ∑ e ∈ F, setWeight L e := by
    calc
      _ = ∑ p ∈ S, setWeight L {p.1, p.2} := by
        apply sum_congr rfl
        intro p hp
        exact (setWeight_pair ((PairSubfamilyWeights.mem_hosts _ _ p).mp hp).2.2.1 L).symm
      _ = _ := PairSubfamilyWeights.weighted_sum (dyadicBlock N) F hF (setWeight L)
  have hpos : 0 ≤ ∑ e ∈ F, setWeight L e := sum_nonneg fun e _ ↦ setWeight_nonneg L e
  rw [heq] at hordered
  linarith only [hordered, hpos]

theorem uniform_high_family (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ AlignedChannelFamilies.families N L b₀, setWeight L e) ≤
        (N : ℝ) ^ (1 + 1 / (b₀ : ℝ) + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := AlignedSourcePairPowers.uniform_height b₀ hb₀ C (ε / 2) (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := OriginalPairHosts.uniform_count C (ε / 2) (by positivity)
  refine ⟨max 2 (max NP NS), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcap : ∀ e ∈ AlignedChannelFamilies.families N L b₀,
      setWeight L e ≤ (N : ℝ) ^ (1 / (b₀ : ℝ) + ε / 2) := by
    intro e he
    obtain ⟨heN, ab, hab, x, y, rfl, hxy, hg⟩ := mem_filter.mp he
    obtain ⟨ha, hablt, hcop, hlow, hheight⟩ := LogHeightUnitChannelFamily.channel_data hab
    have heSub := (mem_powersetCard.mp heN).1
    have hx := heSub (mem_insert_self x {y})
    have hy := heSub (mem_insert_of_mem (mem_singleton_self y))
    have hpower := hp N (by omega) L ab.1 ab.2 x y hband ha (ha.trans hablt) hcop
      (by simpa only [max_eq_right hablt.le] using hlow)
      (by simpa only [max_eq_right hablt.le] using hheight) hx hy hg
    rw [setWeight_pair hxy.ne]
    exact (sub_le_self _ zero_le_one).trans hpower
  calc
    _ ≤ ((PairHostCover.hosts N L).card : ℝ) * (N : ℝ) ^ (1 / (b₀ : ℝ) + ε / 2) :=
      finite_set_support_bound _ _ (Real.rpow_nonneg hn.le _) (filter_subset _ _) hcap
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (1 / (b₀ : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (hs N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_zero_family (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ AlignedChannelFamilies.zeroFamilies N L, setWeight L e) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := AlignedSourcePairPowers.uniform_zero_units C (ε / 2) (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := OriginalPairHosts.uniform_count C (ε / 2) (by positivity)
  refine ⟨max 2 (max NP NS), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcap : ∀ e ∈ AlignedChannelFamilies.zeroFamilies N L, setWeight L e ≤ (N : ℝ) ^ (ε / 2) := by
    intro e he
    obtain ⟨heN, x, y, a, b, rfl, hxy, ha, hb, hcop, hheight, hg, hu⟩ := mem_filter.mp he
    have heSub := (mem_powersetCard.mp heN).1
    have hx := heSub (mem_insert_self x {y})
    have hy := heSub (mem_insert_of_mem (mem_singleton_self y))
    have hpower := hp N (by omega) L a b x y hband ha hb hcop hheight hx hy hg hu
    rw [setWeight_pair hxy.ne]
    exact (sub_le_self _ zero_le_one).trans hpower
  calc
    _ ≤ ((PairHostCover.hosts N L).card : ℝ) * (N : ℝ) ^ (ε / 2) :=
      finite_set_support_bound _ _ (Real.rpow_nonneg hn.le _) (filter_subset _ _) hcap
    _ ≤ (N : ℝ) ^ (1 + ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right (hs N (by omega) L hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_height_one_separated (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ BoundaryAlignedPairs.channel N L 1 1 \ ClosePairs.pairs (dyadicBlock N) L,
        setWeight L e) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀, hbound⟩ := uniform_zero_family C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hsub : BoundaryAlignedPairs.channel N L 1 1 \ ClosePairs.pairs (dyadicBlock N) L ⊆
      AlignedChannelFamilies.zeroFamilies N L := by
    intro e he
    obtain ⟨he, hnot⟩ := mem_sdiff.mp he
    exact (mem_union.mp (BoundaryAlignedPairs.height_one_cover (by omega : 2 ≤ N) he)).resolve_left hnot
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ setWeight_nonneg L e)).trans
    (hbound N hN L hband)

theorem uniform_height_two (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, setWeight L e) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := AlignedSourcePairPowers.uniform_height 2 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NC, hc⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le 16 2 (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max NG NC)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgeom := hg N (by omega) L hband
  have hcap : ∀ e ∈ BoundaryAlignedPairs.channel N L 1 2,
      setWeight L e ≤ (N : ℝ) ^ (1 / 2 + ε / 2) := by
    intro e he
    obtain ⟨x, y, hx, hy, rfl, hxy, halign⟩ := BoundaryAlignedPairs.data he
    have hheight : max 1 2 ≤ (L + 1) ^ 3 := by
      norm_num only [max_eq_right (by decide : 1 ≤ 2)]
      exact hgeom.2.2.1.trans (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
    have hpower := hp N (by omega) L 1 2 x y hband (by decide) (by decide) (by decide)
      (by decide) hheight hx hy halign
    rw [setWeight_pair hxy.ne]
    norm_num only [Nat.cast_ofNat] at hpower
    exact (sub_le_self _ zero_le_one).trans hpower
  have hpoly : 16 * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    have h := hc N (by omega) L hgeom.2.2.2.2.2
    simpa only [Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (L + 1 : ℝ) ^ 2)] using h
  calc
    _ ≤ ∑ _e ∈ BoundaryAlignedPairs.channel N L 1 2, (N : ℝ) ^ (1 / 2 + ε / 2) := sum_le_sum hcap
    _ = ((BoundaryAlignedPairs.channel N L 1 2).card : ℝ) * (N : ℝ) ^ (1 / 2 + ε / 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (16 * ((L + 1 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast BoundaryAlignedPairs.height_two_card N L) (Real.rpow_nonneg hn.le _)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.AlignedSourcePairMass
