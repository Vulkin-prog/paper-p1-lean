module

public import PaperP1.Model.PrivateChannelSources

/-! # Exact transport of the manuscript's fixed real prime threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealPrivateChannelSources

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.GoodEdgeCompression PaperP1.NormalizedUnitCount

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def cutoff (D : ℝ) (L : ℕ) : ℕ := ⌊D * ((L + 1 : ℕ) : ℝ)⌋₊

def realGoodSources (N : ℕ) (D : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    2 ≤ (units a b xy.1 xy.2 L).card ∧
      PrivateAbove (D * ((L + 1 : ℕ) : ℝ)) (NormalizedWindowSets.union a b xy.1 xy.2 L)

def realChannelSources (N : ℕ) (D : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  realGoodSources N D a b L ∪ (realGoodSources N D a b L).image Prod.swap

def realChannelMass (N : ℕ) (D : ℝ) (a b L : ℕ) : ℝ :=
  ∑ xy ∈ realChannelSources N D a b L, infiniteJointMoment L {xy.1, xy.2}

def separatedChannelSources (N : ℕ) (D : ℝ) (a b L : ℕ) : Finset (ℕ × ℕ) :=
  (realChannelSources N D a b L).filter fun xy ↦ xy.1 + L ≤ xy.2 ∨ xy.2 + L ≤ xy.1

def separatedChannelMass (N : ℕ) (D : ℝ) (a b L : ℕ) : ℝ :=
  ∑ xy ∈ separatedChannelSources N D a b L, infiniteJointMoment L {xy.1, xy.2}

theorem privateAbove_floor (H : ℝ) (S : Finset ℕ) (hH : 0 ≤ H) :
    PrivateAbove H S ↔ PrivateAbove (⌊H⌋₊ : ℝ) S := by
  have heq (p : ℕ) : H < (p : ℝ) ↔ (⌊H⌋₊ : ℝ) < p := by
    constructor
    · exact fun h ↦ (Nat.floor_le hH).trans_lt h
    · intro h
      have hn : ⌊H⌋₊ < p := by exact_mod_cast h
      have hs : ⌊H⌋₊ + 1 ≤ p := by omega
      exact (Nat.lt_floor_add_one H).trans_le (by exact_mod_cast hs)
  constructor
  · intro h n hn
    obtain ⟨p, hp, hHp, hparity, hothers⟩ := h n hn
    exact ⟨p, hp, (heq p).mp hHp, hparity, hothers⟩
  · intro h n hn
    obtain ⟨p, hp, hHp, hparity, hothers⟩ := h n hn
    exact ⟨p, hp, (heq p).mpr hHp, hparity, hothers⟩

theorem real_good_sources_eq (N : ℕ) (D : ℝ) (a b L : ℕ) (hD : 0 ≤ D) :
    realGoodSources N D a b L = PrivateChannelSources.goodSources N (cutoff D L) a b L := by
  ext xy
  simp only [realGoodSources, PrivateChannelSources.goodSources, mem_filter, cutoff,
    privateAbove_floor (D * ((L + 1 : ℕ) : ℝ)) (NormalizedWindowSets.union a b xy.1 xy.2 L)
      (mul_nonneg hD (Nat.cast_nonneg (L + 1)))]
  symm
  exact mem_filter

theorem real_channel_sources_eq (N : ℕ) (D : ℝ) (a b L : ℕ) (hD : 0 ≤ D) :
    realChannelSources N D a b L = PrivateChannelSources.channelSources N (cutoff D L) a b L := by
  unfold realChannelSources PrivateChannelSources.channelSources
  rw [real_good_sources_eq N D a b L hD]

theorem real_channel_mass_eq (N : ℕ) (D : ℝ) (a b L : ℕ) (hD : 0 ≤ D) :
    realChannelMass N D a b L = PrivateChannelSources.channelMass N (cutoff D L) a b L := by
  unfold realChannelMass PrivateChannelSources.channelMass
  rw [real_channel_sources_eq N D a b L hD]

theorem cutoff_bounds (D : ℝ) (b L : ℕ) (hD : 2 * (b : ℝ) ≤ D) :
    2 * b * (L + 1) ≤ cutoff D L ∧ cutoff D L ≤ ⌈D⌉₊ * (L + 1) := by
  have hD0 : 0 ≤ D := (by positivity : (0 : ℝ) ≤ 2 * (b : ℝ)).trans hD
  have hDB : 0 ≤ D * ((L + 1 : ℕ) : ℝ) := mul_nonneg hD0 (Nat.cast_nonneg (L + 1))
  unfold cutoff
  constructor
  · apply Nat.le_floor
    have h := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (L + 1))
    exact_mod_cast h
  · have h := (Nat.floor_le hDB).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (Nat.cast_nonneg (L + 1)))
    exact_mod_cast h

theorem real_sources_separated {N a b L : ℕ} (D : ℝ) (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hD : 0 ≤ D)
    {xy : ℕ × ℕ} (hxy : xy ∈ realChannelSources N D a b L) : xy.1 + L ≤ xy.2 ∨ xy.2 + L ≤ xy.1 := by
  rcases mem_union.mp hxy with hf | hs
  · have hg : xy ∈ PrivateChannelSources.goodSources N (cutoff D L) a b L := by
      rw [← real_good_sources_eq N D a b L hD]
      exact hf
    exact Or.inl (PrivateChannelSources.good_sources_separated hN ha hab hcop hlarge hg)
  · obtain ⟨uv, huv, heq⟩ := mem_image.mp hs
    have hg : uv ∈ PrivateChannelSources.goodSources N (cutoff D L) a b L := by
      rw [← real_good_sources_eq N D a b L hD]
      exact huv
    have hsep := PrivateChannelSources.good_sources_separated hN ha hab hcop hlarge hg
    rw [← heq]
    exact Or.inr hsep

theorem separated_mass_eq {N a b L : ℕ} (D : ℝ) (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hD : 0 ≤ D) :
    separatedChannelMass N D a b L = realChannelMass N D a b L := by
  have hf : separatedChannelSources N D a b L = realChannelSources N D a b L :=
    filter_eq_self.mpr (fun xy hxy ↦ real_sources_separated D hN ha hab hcop hlarge hD hxy)
  unfold separatedChannelMass realChannelMass
  rw [hf]

end PaperP1.RealPrivateChannelSources
